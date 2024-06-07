use std::collections::BTreeMap;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    parse_macro_input, Attribute, Field,
    Fields, GenericParam, Ident, Item, ItemEnum, ItemStruct, Meta, MetaList,
    MetaNameValue, PathArguments, Token, Type, TypeParam, Variant,
};

/// Generate a `map` function for a given type that maps across all its type parameters.
/// i.e.
/// ```
/// #[derive(...)]
/// // optional: setting a name for the type parameters, doesn't affect the structure
/// // of the data in any way, just the variable names.
/// #[derive_n_functor(B = second_type_param)]
/// // We can also choose a different map name, the default being `map`.
/// // This will recurse down to child elements without a custom `map_with` declaration.
/// // #[derive_n_functor(map_name = different_map)]
/// struct Data<A, B> {
///     a: A,
///     // The map_with argument is an arbitrary expression.
///     #[map_with(Option::map)]
///     b: Option<B>
/// }
/// ```
///
/// Will generate a mapping function of the form: `Data::map(self, map_a: impl Fn(A) -> A2, map_second_type_param: impl B -> B2) -> Data<A2, B2>`.
///
/// See examples and use `cargo-expand` to see how different code generates.
///
/// Currently works with enums and structs. 
/// 
/// Caveats:
/// - Does not work with data structures that have lifetimes or constants in them at this time. 
/// - Does not currently work well with i.e. tuples where one of the types within is a type parameter. if you need to deal with this, write an external function that applies the mappings (see examples.)
#[proc_macro_attribute]
pub fn derive_n_functor(args: TokenStream, item: TokenStream) -> TokenStream {
    let _args: TokenStream2 = args.clone().into();
    let _item: TokenStream2 = item.clone().into();
    let args = Args::from_token_stream(args);
    let mut input = parse_macro_input!(item as Item);
    let output = match &mut input {
        Item::Enum(_enum) => AbstractFunctorFactory::from_item_enum(args, _enum),
        Item::Struct(_struct) => AbstractFunctorFactory::from_item_struct(args, _struct),
        _ => {
            quote_spanned! {_args.span() => compile_error!("Could not derive n-functor for this, it is neither an enum or struct.")}
        }
    };
    quote! {
        #input
        #output
    }
    .into()
}

struct Args {
    pub parameter_names: BTreeMap<Ident, Ident>,
    pub mapping_name: String,
    // Alternative functions for mapping for specific fields.
    // pub alt_functions: BTreeMap<Ident, TokenStream>,
}

impl Args {
    fn from_token_stream(stream: TokenStream) -> Self {
        let parsed_attrs: Punctuated<MetaNameValue, Token![,]> =
            Parser::parse2(Punctuated::parse_terminated, stream.into()).unwrap();
        Args::from_iter(parsed_attrs.into_iter())
    }

    fn from_iter(input: impl Iterator<Item = MetaNameValue>) -> Self {
        let search_for_mapping_token = Ident::new("map_name", Span::call_site());
        let mut mapping_name = "map".to_string();
        let parameter_names = input
            .filter_map(|name_val| {
                if name_val.path.segments.last().unwrap().ident == search_for_mapping_token {
                    // found the map renaming arg so skip this one after renaming mapping_name
                    if let syn::Expr::Path(path) = name_val.value {
                        mapping_name = path.path.segments.last()?.ident.to_string();
                    }
                    // return none as we've consumed this input.
                    return None
                }
                // continue to processing 
                let ty_ident = &name_val.path.segments.last()?.ident;
                let rename_ident = &match &name_val.value {
                    syn::Expr::Path(path) => path.path.segments.last(),
                    _ => None,
                }?
                .ident;
                Some((ty_ident.clone(), rename_ident.clone()))
            })
            .collect();
        Self { parameter_names, mapping_name }
    }

    fn get_suffix_for(&self, ident: &Ident) -> Ident {
        self.parameter_names
            .get(ident)
            .cloned()
            .unwrap_or_else(|| Ident::new(&format!("{ident}"), Span::call_site()))
    }

    fn get_whole_map_name(&self, ident: &Ident) -> Ident {
        let suffix = self.get_suffix_for(ident);
        Ident::new(&format!("map_{suffix}"), Span::call_site())
    }

    fn get_map_all_name(&self) -> Ident {
        Ident::new(&self.mapping_name, Span::call_site())
    }
}

enum FieldMapping {
    Trivial(Ident),
    SubMapForArgs(Vec<Ident>),
}

type FieldNameMapping = Option<Vec<Ident>>;

struct AbstractFunctorFactory {
    pub args: Args,
    // this is a vec for reasons of preserving order of type parameters.
    pub type_maps_to_type: Vec<(Ident, Ident)>,
    pub type_name: Ident,
}

impl AbstractFunctorFactory {
    fn from_generics<'a>(
        args: Args,
        generics: impl Iterator<Item = &'a GenericParam>,
        type_name: Ident,
    ) -> Self {
        let mut type_maps_to_type = vec![];
        for generic in generics {
            match generic {
                GenericParam::Lifetime(_) => {}
                GenericParam::Type(ty) => type_maps_to_type.push((
                    ty.ident.clone(),
                    Ident::new(&format!("{}2", ty.ident), Span::call_site()),
                )),
                GenericParam::Const(_) => {}
            }
        }
        AbstractFunctorFactory {
            args,
            type_maps_to_type,
            type_name,
        }
    }

    fn from_item_enum(args: Args, source: &mut ItemEnum) -> TokenStream2 {
        let name = source.ident.clone();
        let factory = AbstractFunctorFactory::from_generics(
            args,
            source.generics.params.iter(),
            source.ident.clone(),
        );
        let map_name = factory.args.get_map_all_name();
        let (impl_gen, type_gen, where_clause) = source.generics.split_for_impl();
        let mapped_params: Punctuated<TypeParam, Token![,]> = factory
            .type_maps_to_type
            .iter()
            .map(|a| TypeParam::from(a.1.clone()))
            .collect();
        let fn_args = factory.make_fn_arguments();
        let implemented: Punctuated<TokenStream2, Token![,]> = source
            .variants
            .iter_mut()
            .map(|variant| factory.implement_body_for_variant(variant))
            .collect();
        quote! {
            impl #impl_gen #name #type_gen #where_clause {
                pub fn #map_name<#mapped_params>(self, #fn_args) -> #name<#mapped_params> {
                    match self {
                        #implemented
                    }
                }
            }
        }
    }

    fn from_item_struct(args: Args, source: &mut ItemStruct) -> TokenStream2 {
        let name = source.ident.clone();
        let factory = AbstractFunctorFactory::from_generics(
            args,
            source.generics.params.iter(),
            source.ident.clone(),
        );
        let map_name = factory.args.get_map_all_name();
        let (impl_gen, type_gen, where_clause) = source.generics.split_for_impl();
        let mapped_params: Punctuated<TypeParam, Token![,]> = factory
            .type_maps_to_type
            .iter()
            .map(|a| TypeParam::from(a.1.clone()))
            .collect();
        let fn_args = factory.make_fn_arguments();
        let (fields, names_for_unnamed) = Self::unpack_fields(&source.fields);
        let expanded = match source.fields {
            Fields::Named(_) => quote! {#name {#fields}},
            Fields::Unnamed(_) => quote! {#name(#fields)},
            Fields::Unit => quote! {#name},
        };
        let implemented =
            factory.apply_mapping_to_fields(&mut source.fields, name.clone(), names_for_unnamed);
        quote! {
            impl #impl_gen #name #type_gen #where_clause {
                pub fn #map_name<#mapped_params>(self, #fn_args) -> #name<#mapped_params> {
                    let #expanded = self;
                    #implemented
                }
            }
        }
    }

    fn implement_body_for_variant(&self, variant: &mut Variant) -> TokenStream2 {
        let type_name = &self.type_name;
        let name = &variant.ident;
        let (unpacked, name_mapping) = Self::unpack_fields(&variant.fields);
        match variant.fields {
            Fields::Named(_) => {
                let implemented =
                    self.apply_mapping_to_fields(&mut variant.fields, name.clone(), name_mapping);
                quote! {
                    #type_name::#name{#unpacked} => #type_name::#implemented
                }
            }
            Fields::Unnamed(_) => {
                let implemented =
                    self.apply_mapping_to_fields(&mut variant.fields, name.clone(), name_mapping);
                quote! {
                    #type_name::#name(#unpacked) => #type_name::#implemented
                }
            }
            Fields::Unit => quote! {
                #type_name::#name => #type_name::#name
            },
        }
    }

    /// The behaviour for this is such that the order of generics for the container type is followed best as possible.
    fn get_mappable_generics_of_type(&self, ty: &Type) -> Option<FieldMapping> {
        if let Type::Path(path) = ty {
            let last_segment = path.path.segments.last();
            // unwraps here because segments' length is checked to be >0 right here.
            if path.path.segments.len() == 1
                && self
                    .type_maps_to_type
                    .iter()
                    .any(|(gen, _)| *gen == last_segment.unwrap().ident)
            {
                // the type is a path with 1 segment whose identifier matches a type parameter, so it's a trivial case.
                return Some(FieldMapping::Trivial(last_segment.unwrap().ident.clone()));
            }
        }
        let mut buffer = Vec::new();
        self.recursive_get_generics_of_type_to_buffer(ty, &mut buffer);
        (!buffer.is_empty()).then_some(FieldMapping::SubMapForArgs(buffer))
    }

    // needs to take a vector as its way of knowing what types have been found to preserve order within the
    // recursed types.
    fn recursive_get_generics_of_type_to_buffer(&self, ty: &Type, buffer: &mut Vec<Ident>) {
        match ty {
            Type::Array(array) => {
                self.recursive_get_generics_of_type_to_buffer(&array.elem, buffer)
            }
            Type::Paren(paren) => {
                self.recursive_get_generics_of_type_to_buffer(&paren.elem, buffer)
            }
            Type::Path(path) => {
                if let Some(segment) = path.path.segments.last().filter(|segment| {
                    self.type_maps_to_type
                        .iter()
                        .any(|(gen, _)| segment.ident == *gen)
                }) {
                    if !buffer.contains(&segment.ident) {
                        buffer.push(segment.ident.clone());
                    }
                    if let PathArguments::AngleBracketed(generics) = &segment.arguments {
                        for generic in &generics.args {
                            if let syn::GenericArgument::Type(ty) = generic {
                                self.recursive_get_generics_of_type_to_buffer(ty, buffer)
                            }
                        }
                    }
                }
                // this needs to be out of the last check otherwise we don't properly recurse on non-type-params.
                if let Some(PathArguments::AngleBracketed(generics)) = &path.path.segments.last().map(|segment| &segment.arguments) {
                    for generic in &generics.args {
                        if let syn::GenericArgument::Type(ty) = generic {
                            self.recursive_get_generics_of_type_to_buffer(ty, buffer)
                        }
                    }
                }
            }
            Type::Tuple(tuple) => {
                for ty in &tuple.elems {
                    self.recursive_get_generics_of_type_to_buffer(ty, buffer)
                }
            }
            _ => {}
        }
    }

    fn unpack_fields(fields: &Fields) -> (TokenStream2, FieldNameMapping) {
        match fields {
            Fields::Named(named) => {
                let names: Punctuated<Ident, Token![,]> = named
                    .named
                    .iter()
                    .map(|field| field.ident.clone().unwrap())
                    .collect();
                let tokens = quote! {
                    #names
                };
                (tokens, None)
            }
            Fields::Unnamed(unnamed) => {
                let faux_names: Punctuated<Ident, Token![,]> = unnamed
                    .unnamed
                    .iter()
                    .enumerate()
                    .map(|(num, _)| Ident::new(&format!("field_{num}"), Span::call_site()))
                    .collect();
                let tokens = quote! {
                    #faux_names
                };
                (tokens, Some(faux_names.into_iter().collect()))
            }
            Fields::Unit => (quote! {}, None),
        }
    }

    fn apply_mapping_to_fields(
        &self,
        fields: &mut Fields,
        name: Ident,
        names_for_unnamed: FieldNameMapping,
    ) -> TokenStream2 {
        match fields {
            Fields::Named(named) => {
                let mapped: Punctuated<TokenStream2, Token![,]> = named
                    .named
                    .iter_mut()
                    .map(|field| {
                        // we can unwrap as it's a named field.
                        let field_name = field.ident.clone().unwrap();
                        let new_field_content =
                            self.apply_mapping_to_field_ref(field, quote! {#field_name});
                        quote! {
                            #field_name: #new_field_content
                        }
                    })
                    .collect();
                let implemented = mapped.to_token_stream();
                quote! {
                    #name {
                        #implemented
                    }
                }
            }
            Fields::Unnamed(unnamed) => {
                let names = names_for_unnamed.unwrap();
                let mapped: Punctuated<TokenStream2, Token![,]> = unnamed
                    .unnamed
                    .iter_mut()
                    .enumerate()
                    .map(|(field_num, field)| {
                        let name_of_field = &names[field_num];
                        let field_ref = quote! {#name_of_field};
                        let new_field_content = self.apply_mapping_to_field_ref(field, field_ref);
                        quote! {
                            #new_field_content
                        }
                    })
                    .collect();
                quote! {
                    #name(#mapped)
                }
            }
            Fields::Unit => quote! {#name},
        }
    }

    fn apply_mapping_to_field_ref(
        &self,
        field: &mut Field,
        field_ref: TokenStream2,
    ) -> TokenStream2 {
        match self.get_mappable_generics_of_type(&field.ty) {
            Some(mapping) => match mapping {
                FieldMapping::Trivial(type_to_map) => {
                    let map = self.args.get_whole_map_name(&type_to_map);
                    quote! {
                        #map(#field_ref)
                    }
                }
                // attempt recursion on the type.
                FieldMapping::SubMapForArgs(sub_maps) => {
                    let map_all_name = self.args.get_map_all_name();
                    let all_fns: Punctuated<TokenStream2, Token![,]> = sub_maps
                        .iter()
                        .map(|ident| {
                            let ident = self.args.get_whole_map_name(ident);
                            quote! {&#ident}
                        })
                        .collect();
                    match FieldArg::find_in_attributes(field.attrs.iter()) {
                        Some(FieldArg { alt_function }) => {
                            FieldArg::remove_from_attributes(&mut field.attrs);
                            quote! {
                                (#alt_function)(#field_ref, #all_fns)
                            }
                        }
                        None => {
                            quote! {
                                #field_ref.#map_all_name(#all_fns)
                            }
                        }
                    }
                }
            },
            // There's no need to map, so we just move.
            None => quote! {#field_ref},
        }
    }

    fn make_fn_arguments(&self) -> TokenStream2 {
        let mapped: Punctuated<TokenStream2, Token![,]> = self
            .type_maps_to_type
            .iter()
            .map(|(from, to)| {
                let fn_name = self.args.get_whole_map_name(from);
                // it's this or TypedPat / PatTyped
                // don't need to trailing comma this cos the punctuated type does that for us.
                quote! {
                    #fn_name: impl Fn(#from) -> #to
                }
            })
            .collect();
        mapped.into_token_stream()
    }
}

struct FieldArg {
    pub alt_function: TokenStream2,
}

impl FieldArg {
    fn map_with_attr_ident() -> Ident {
        Ident::new("map_with", Span::call_site())
    }

    fn remove_from_attributes(attributes: &mut Vec<Attribute>) {
        let ident_to_check = Self::map_with_attr_ident();
        // reverse the iterator so that we can remove indices easily.
        let to_remove: Vec<_> = attributes
            .iter()
            .enumerate()
            .rev()
            .filter_map(|(num, attribute)| match &attribute.meta {
                Meta::Path(_) => None,
                Meta::List(meta) => {
                    let last = meta.path.segments.last()?;
                    (last.ident == ident_to_check).then_some(num)
                }
                Meta::NameValue(_) => None,
            })
            .collect();
        for remove in to_remove {
            attributes.remove(remove);
        }
    }

    fn find_in_attributes<'a>(mut attributes: impl Iterator<Item = &'a Attribute>) -> Option<Self> {
        attributes.find_map(|attribute| match &attribute.meta {
            Meta::Path(_) => None,
            Meta::List(meta) => Self::from_meta_list(meta),
            Meta::NameValue(_) => None,
        })
    }

    fn from_meta_list(meta: &MetaList) -> Option<Self> {
        let ident_to_check = Self::map_with_attr_ident();
        if meta.path.segments.iter().last().map(|x| &x.ident) == Some(&ident_to_check) {
            Some(Self {
                alt_function: meta.tokens.clone(),
            })
        } else {
            None
        }
    }
}
// #[proc_macro_attribute]
// pub fn derive_n_foldable(attr: TokenStream, item: TokenStream) -> TokenStream {
//     unimplemented!()
// }
