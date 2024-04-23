#[macro_export]
macro_rules! mul_add {
    ($a:expr, $b:expr, $c:expr) => {
        if cfg!(feature = "fma") {
            f64::mul_add($a, $b, $c)
        } else {
            $a * $b + $c
        }
    };
}
