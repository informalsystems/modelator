use std::convert::Into;

// Conversion between tuples and arrays
// Modeled after https://stackoverflow.com/a/44043197
// Currently limited to the length at most 3.
// Consider implementing via a macro

pub trait ConvFrom<T> {
    fn conv_from(t: T) -> Self;
}

pub trait ConvInto<U> {
    fn conv_into(self) -> U;
}

impl<T, U> ConvInto<U> for T
where
    U: ConvFrom<T>,
{
    fn conv_into(self) -> U {
        <U as ConvFrom<T>>::conv_from(self)
    }
}

impl<T> ConvFrom<()> for [T; 0] {
    fn conv_from(_: ()) -> Self {
        []
    }
}

impl<T> ConvFrom<[T; 0]> for () {
    fn conv_from(_: [T; 0]) -> Self {
        ()
    }
}

impl<T, A> ConvFrom<(A,)> for [T; 1]
where
    A: Into<T>,
{
    fn conv_from(t: (A,)) -> Self {
        [t.0.into()]
    }
}

impl<T, A> ConvFrom<[T; 1]> for (A)
where
    T: Into<A> + Copy,
{
    fn conv_from(t: [T; 1]) -> Self {
        (t[0].into())
    }
}

impl<T, A, B> ConvFrom<(A, B)> for [T; 2]
where
    A: Into<T>,
    B: Into<T>,
{
    fn conv_from(t: (A, B)) -> Self {
        [t.0.into(), t.1.into()]
    }
}

impl<T, A, B> ConvFrom<[T; 2]> for (A, B)
where
    T: Into<A> + Into<B> + Copy,
{
    fn conv_from(t: [T; 2]) -> Self {
        (t[0].into(), t[1].into())
    }
}

impl<T, A, B, C> ConvFrom<(A, B, C)> for [T; 3]
where
    A: Into<T>,
    B: Into<T>,
    C: Into<T>,
{
    fn conv_from(t: (A, B, C)) -> Self {
        [t.0.into(), t.1.into(), t.2.into()]
    }
}

impl<T, A, B, C> ConvFrom<[T; 3]> for (A, B, C)
where
    T: Into<A> + Into<B> + Into<C> + Copy,
{
    fn conv_from(t: [T; 3]) -> Self {
        (t[0].into(), t[1].into(), t[2].into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let array: [i64; 3] = (1u32, 2i16, 3i8).conv_into();
        assert_eq!(array, [1, 2, 3]);
        //println!("{:?}", array);

        let tuple: (i64, i32, i16) = [1i16, 2i16, 3i16].conv_into();
        assert_eq!(tuple, (1, 2, 3));
        //println!("{:?}", tuple);
    }
}
