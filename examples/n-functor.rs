use n_functor::*;

#[derive_n_functor(A = ayy, B = bee)]
pub struct Three<A, B, C> {
    pub a: A,
    pub a_2: A,
    pub b: B,
    pub c: C,
    pub irrelevant: String,
}

impl<A, B, C> Three<A, B, C> {
    fn hello(&self) {
        println!("The separate impl blocks don't interfere.")
    }
}

// a custom name for the mapping function.
#[derive_n_functor(map_name = endofunctor_on_rust_category)]
pub struct CustomMap<A> {
    a: A,
}

impl CustomMap<usize> {
    pub fn next(self) -> Self {
        self.endofunctor_on_rust_category(|x| x + 1)
    }
}

#[derive_n_functor]
pub struct Zero;

#[derive_n_functor]
pub struct Two<A, B>(A, B);

#[derive_n_functor]
pub enum AyyBee<A, B> {
    One(A),
    Two(B),
    Three {
        a: A,
        b: B,
    },
    Four(A, B, A, B, A),
    Five,
    Six(
        #[map_with(|opt: Option<_>, ayy, bee| opt.map(|two: Two<A, B>| two.map(ayy, bee)))]
        Option<Two<A, B>>,
    ),
}

fn id<A>(a: A) -> A {
    a
}

// tuples are an issue because the macro doesn't expand them like unnamed structs / enums
// and there would need to be a recursive destructuring of them to make sure tuples in tuples
// work appropriately. Un/fortunately this is a side project to support other projects,
// and time is not free, so I have yet to do that.
#[derive_n_functor]
pub struct TuplesAreDire<A, B>(#[map_with(sorry_for_tuples, sorry_for_tuples_map_res)] (A, B));

fn sorry_for_tuples<A, B, A2, B2>(
    (a, b): (A, B),
    f_a: impl Fn(A) -> A2,
    f_b: impl Fn(B) -> B2,
) -> (A2, B2) {
    (f_a(a), f_b(b))
}

fn sorry_for_tuples_map_res<A, B, A2, B2, E>(
    (a, b): (A, B),
    f_a: impl Fn(A) -> Result<A2, E>,
    f_b: impl Fn(B) -> Result<B2, E>,
) -> Result<(A2, B2), E> {
    Ok((f_a(a)?, f_b(b)?))
}

#[derive_n_functor]
pub struct Recursion<A, B> {
    moi: A,
    #[map_with(|list: [A; 5], a| list.into_iter().map(a).collect::<Vec<_>>().try_into().unwrap_or_else(|_| unimplemented!()))]
    x: [A; 5],
    a_b: AyyBee<A, B>,
    #[map_with(Option::map, map_res_for_option)]
    opt: Option<A>,
    #[map_with(|opt: Option<_>, f| opt.map(|opt: Option<_>| opt.map(f)), Self::map_res_for_option_option)]
    opt2: Option<Option<B>>,
}

fn map_res_for_option<A, A2, E>(
    opt: Option<A>,
    f: impl Fn(A) -> Result<A2, E>,
) -> Result<Option<A2>, E> {
    match opt {
        Some(value) => Ok(Some(f(value)?)),
        None => Ok(None),
    }
}

impl<A, B> Recursion<A, B> {
    fn map_res_for_option_option<B2, E>(
        opt: Option<Option<B>>,
        f: impl Fn(B) -> Result<B2, E>,
    ) -> Result<Option<Option<B2>>, E> {
        match opt {
            Some(Some(inner)) => Ok(Some(Some(f(inner)?))),
            // unreachable because the inner is already reached in the above case
            lacks_inner => Ok(lacks_inner.map(|opt| opt.map(|_| unreachable!()))),
        }
    }
}

#[derive_n_functor]
pub struct Opt<A>(Option<A>);

fn main() {
    let other = Three {
        a: 32u32,
        a_2: 33u32,
        b: 64u64,
        c: 8u8,
        irrelevant: "Hallo".to_string(),
    };
    other.hello();
    let x = other.map(id, |_| 45i32, id);
    x.hello();
}
