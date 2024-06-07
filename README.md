# n-functor ![](https://img.shields.io/crates/v/n-functor)

You find yourself writing the same `map` function on 15 different recursing types with 6 type parameters. Time spent writing `map_all` for `MyData<A,B,C,D,E,F>` is time poorly spent. It should be more simple than this, surely some mode of derive? Ah, but rust's type system does not support higher-kinded types. This is a piece of information you know because of a misspent youth.

Instead you like many others wish for someone else to have written a macro to do this for you. Ah, but there's complicating factors, like the orphan rule and so on. You won't write this yourself, of course. Procedural macros are scary, your experiments with them fruitless and stressful.

There is always a someone else who should have done this already with our infrastructure, and eventually you find yourself as that someone else. Maybe being that someone else will be a boon to your employability, maybe it will be a final year project, maybe it will be an academic career, a bonus, an icebreaker at the next tech meetup. But to be that someone else is a pain, don't you feel relief when that someone else is _someone else_?

This is no matter, what you need right now is something to write a trivial to imagine but pain to repeat map function for your complicated type. You do not wish to spill your own blood over this kind of project. Do not worry, dearest and most beloved software engineer, I have spilt my blood for you as today's Someone Else:

```rust
#[derive(...)]
// optional: setting a name for the type parameters, doesn't affect the structure
// of the data in any way, just the variable names.
#[derive_n_functor(B = second_type_param)]
// We can also choose a different map name, the default being `map`.
// This will recurse down to child elements without a custom `map_with` declaration.
// #[derive_n_functor(map_name = different_map)]
struct Data<A, B> {
    a: A,
    // The map_with argument is an arbitrary expression.
    #[map_with(Option::map)]
    b: Option<B>
}

// Expands to this, merely at the cost of the soul of the author.
impl <A, B> Data<A, B> {
    pub fn map<A2, B2>(self, map_A: impl Fn(A) -> A2, map_second_type_param: impl Fn(B) -> B2) -> Data<A2, B2> {
        let Data {a, b} = self;
        Data {
            a: map_A(a),
            b: (Option::map)(b, map_second_type_param),
        }
    }
}
```

## Features

- Support for Structs and Enums, with both named and unnamed fields (including in enum variants).
- Custom names for type parameters in the map function, through the form `#[derive_n_functor(T = name_for_t)]`.
- Custom name for the implemented map function via `#[derive_n_functor(map_name = custom_map)]`.
- Custom mapping for fields with non-trivial types, via the `#[map_with(...)]` attribute, where you can put in any function (including lambdas) to account for difficult cases.
- Recursive calling on fields with applicable type parameters.
- See examples for a terrible aftermath of my edge case testing (at time of writing, all those compile).

## Limitations

Currently the following aren't supported:
- Types with non-type parameters i.e. const generics, lifetimes.
- Tuples with are difficult to handle, see [examples/n-functor.rs](/examples/n-functor.rs) for how to format `#[map_with(...)]` for tuples.

Other limitations:
- Only a self-consuming map function is generated at this time. No `map_ref(&self, ...)`, for now. No promises though. This may be mutually exclusive with supporting lifetime parameters in the future.

## Design

This does not work off any traits in any way, this is due to current limitations of rust's type system. This leaves something to be desired from a pure functional programming point of view, but this is inherent to rusts own limitations. To ask for a trait-bound system that doesn't cause immense stress on a user who has not passed through the fire of advanced haskell is maybe a fair ask for a crate called `n-functor`, but I present you with the next-best option.

## License

This project is under the MIT license. I do not like having it under the MIT license, I have spent too much time in my life feeling as if contributing to open source in a way like this leaves me culpable to the worst of whoever ends up using what I publish. If I write a simple utility with wide reach, what does that mean when someone uses it in missile software? How many others are consumed with thoughts like this? On a philosophical level, how many degrees of separation does it take before you're in the clear?

And what about machine learning systems eating this source to regurgitate in someone else's codebase? An impression of my work, my pain, indexed in microsoft's least efficient database ever, singing vile echoes in my voice, for the profit of someone else and without credit in any way? Contributing to open source used to be a way of gaining social capital, a way for people to cash in their time for connections and opportunity and clout and of course last of all you got software for free and on an epistemic level it was difficult to make that software malicious. [To a degree](https://www.cs.cmu.edu/~rdriley/487/papers/Thompson_1984_ReflectionsonTrustingTrust.pdf). An imperfect mode of production, but one where community was found and it was proof that people just like to work on things together and that the profit motive was, like every other supposed axiom, as malleable and bound by flesh as all rhetoric. But now it is a commons enclosed by every software company under the sun chasing a machine god they continuously fail to birth but insist has brought a new world.

I ask that you use this to build a better world. I ask that you quit your job at raytheon. I ask that you question your company's place in the world on a political level. I ask that you funnel your silicon valley income into the lives of the underclasses. I ask for a free Palestine. I ask for a really peaceful world, not one where a lop-sided imperial-colonial violence is called peace. I ask for self-awareness and for that to not be where you stagnate. I ask that you read. I ask that you talk. I ask that you engage in a praxis that could make the world truly a better place for every heart that still beats, where every heart that has been stopped beating could have flourished among the rest. This is software.
