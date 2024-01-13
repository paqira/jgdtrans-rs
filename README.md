# jgdtrans

```rust
use jgdtrans::{Point, SemiDynaEXE};

fn main -> Result<(), Box<dyn Error>> {
    // Deserialize par-formatted file, e.g. SemiDyna2023.par
    let s = fs::read_to_string("SemiDyna2023.par").expect("file not found 'SemiDyna2023.par'");
    let tf = SemiDynaEXE::from_str(&s)?;

    // Make the origin of transformation
    let origin = Point::try_new(35.0, 135.0, 2.34)?;
    // Prints Origin: Point { latitude: 35.0, longitude: 135.0, altitude: 2.34 }
    println!("Origin: {origin:?}");

    // Perform forward transformation resulting a Point
    let result = tf.forward(&origin)?;
    // Prints Forward: Point { latitude: 34.99999831111111, longitude: 135.00000621666666, altitude: 2.33108 }
    println!("Forward: {result:?}");

    // Perform backward transformation
    let p = tf.backward(&result)?;
    // Prints Backward: Point { latitude: 34.999999999999986, longitude: 135.0, altitude: 2.339999999105295 }
    println!("Backward: {p:?}");

    // Perform verified backward transformation
    // that the error from the exact solution is less than GIAJ parameter error
    let q = tf.backward_safe(&result)?;
    // Prints Verified Backward: Point { latitude: 35.0, longitude: 135.0, altitude: 2.3400000000005847 }
    println!("Verified Backward: {q:?}");

    Ok(())
}
```

Unofficial Rust impl. of coordinate transformer by _Gridded Correction Parameter_
which Geospatial Information Authority of Japan (GIAJ, formerly GSIJ) distributing.

国土地理院が公開している .par ファイルによる変換（逆変換）の非公式な実装です。

Features:

- Offline transformation (no web API)
  - オフライン変換（web API 不使用）
- Support both original forward/backward transformation
  - 順変換と逆変換の両方をサポート
- Support verified backward transformation
  - 精度を保証した逆変換のサポート
- Support all TKY2JGD, PatchJGD, PatchJGD(H), HyokoRev, SemiDynaEXE, geonetF3 and ITRF2014 (POS2JGD),
  e.g. Tokyo Datum to JGD2000 (EPSG:4301 to EPSG:4612) and JGD2000 to JGD2011 (EPSG:4612 to EPSG:6668)
  - 上記の全てをサポート
- Clean implementation
  - 保守が容易な実装
- No dependency; depends on [`serde`](https://crates.io/crates/serde) and
  [`serde_repr`](https://crates.io/crates/serde_repr) creates only if `serde` feature on
  - 依存パッケージなし

`jdgtrans` requires nightly channel so far.

This package does not contain parameter files, download it from GIAJ.

このパッケージはパラメータファイルを提供しません。公式サイトよりダウンロードしてください。

## Optional Features

- `serde`: supports serialization/deserialization by [`serde` create](https://crates.io/crates/serde).

## Licence

MIT or Apache-2.0

## Reference

1. Geospatial Information Authority of Japan (GIAJ, 国土地理院):
   <https://www.gsi.go.jp/>,
   (English) <https://www.gsi.go.jp/ENGLISH/>.
2. _TKY2JGD for Windows Ver.1.3.79_ (reference implementation): <https://www.gsi.go.jp/sokuchikijun/tky2jgd_download.html>,
   released under [国土地理院コンテンツ利用規約](https://www.gsi.go.jp/kikakuchousei/kikakuchousei40182.html)
   which compatible to CC BY 4.0.
3. Python implementation: <https://github.com/paqira/JGDtrans-py>.
