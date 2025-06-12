use n_functor::*;

#[derive(Debug)]
enum MyError {
    FailedOpt,
}

#[derive_n_functor(impl_map_res = true)]
pub struct Two<A, B>(A, B);

#[derive_n_functor(impl_map_res = true)]
pub struct Opt<A>(#[map_with(Option::map, map_res_for_option)] Option<A>);

fn map_res_for_option<A, A2, E>(
    opt: Option<A>,
    f: impl Fn(A) -> Result<A2, E>,
) -> Result<Option<A2>, E> {
    match opt {
        Some(value) => Ok(Some(f(value)?)),
        None => Ok(None),
    }
}

fn resultant_maps() -> Result<(), MyError> {
    let two = Two(5u8, "seven");
    let mapped_two = two.map_res(|num| Ok(num == 5), |s| Ok(s.len()))?;
    println!("{}, {}", mapped_two.0, mapped_two.1);
    let this_is_not_reached: Opt<u8> = Opt(Some(0)).map_res(|_| Err(MyError::FailedOpt))?;
    println!(
        "This won't work, because we errored out! you can't see {:?}",
        this_is_not_reached.0
    );
    Ok(())
}

pub fn main() {
    println!("The result of this program was: {:?}", resultant_maps());
}
