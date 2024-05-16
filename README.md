# jgdtrans for Rust

Unofficial coordinate transformer by _Gridded Correction Parameter_
which Geospatial Information Authority of Japan (GIAJ, formerly GSIJ) distributing
for Rust.

国土地理院が公開している .par ファイルによる変換（逆変換）の非公式な実装です。

Features:

- Offline transformation (no web API)
    - オフライン変換（web API 不使用）
- Supports both original forward/backward transformation
    - 順変換と逆変換の両方をサポート
- Supports verified backward transformation
    - 精度を保証した逆変換のサポート
- Supports all [TKY2JGD], [PatchJGD], [PatchJGD(H)], [HyokoRev], [SemiDynaEXE]
  and [POS2JGD] (geonetF3 and ITRF2014)
    - For example, Tokyo Datum to JGD2000 ([EPSG:4301] to [EPSG:4612])
      and JGD2000 to JGD2011 ([EPSG:4612] to [EPSG:6668])
    - 上記の全てをサポート
- Clean implementation
    - 保守が容易な実装
- No dependency
    - 依存パッケージなし

`jdgtrans` requires nightly channel, it depends on a `float_next_up_down` feature.

[TKY2JGD]: https://www.gsi.go.jp/sokuchikijun/tky2jgd.html
[PatchJGD]: https://vldb.gsi.go.jp/sokuchi/surveycalc/patchjgd/index.html
[PatchJGD(H)]: https://vldb.gsi.go.jp/sokuchi/surveycalc/patchjgd_h/index.html
[HyokoRev]: https://vldb.gsi.go.jp/sokuchi/surveycalc/hyokorev/hyokorev.html
[SemiDynaEXE]: https://vldb.gsi.go.jp/sokuchi/surveycalc/semidyna/web/index.html
[POS2JGD]: https://positions.gsi.go.jp/cdcs

[EPSG:4301]: https://epsg.io/4301
[EPSG:4612]: https://epsg.io/4612
[EPSG:6668]: https://epsg.io/6668

## Optional Features

- `serde`: supports serialization/deserialization by [`serde` crate][serde],
           this requires dependency on [`serde`][serde].

[serde]: https://crates.io/crates/serde
[fma]: https://en.wikipedia.org/wiki/Multiply–accumulate_operation

## Usage

This package does not contain parameter files, download it from GIAJ.

このパッケージはパラメータファイルを提供しません。公式サイトよりダウンロードしてください。

Sample code:

```rust
use std::error::Error;
use std::fs;

use jgdtrans::{Point, Transformer, Format};

fn main() -> Result<(), Box<dyn Error>> {
    // Deserialize par-formatted file, e.g. SemiDyna2023.par
    let s = fs::read_to_string("SemiDyna2023.par").expect("file not found 'SemiDyna2023.par'");
    let tf = Transformer::from_str(&s, Format::SemiDynaEXE)?;

    // Make the origin of transformation
    let origin = Point::new(35.0, 135.0, 2.34);
    // Prints Point { latitude: 35.0, longitude: 135.0, altitude: 2.34 }
    println!("{origin:?}");

    // Perform forward transformation resulting a Point
    let result = tf.forward(&origin)?;
    // Prints Point { latitude: 34.99999831111111, longitude: 135.00000621666666, altitude: 2.33108 }
    println!("{result:?}");

    // Perform backward transformation
    let p = tf.backward(&result)?;
    // Prints Point { latitude: 35.0, longitude: 135.0, altitude: 2.34 }
    println!("{p:?}");

    // Perform backward transformation compatible to the GIAJ web app/APIs
    let q = tf.backward_compat(&result)?;
    // Prints Point { latitude: 34.999999999999986, longitude: 135.0, altitude: 2.339999999105295 }
    println!("{q:?}");

    Ok(())
}
```

## Licence

MIT or Apache-2.0

## Reference

1. Geospatial Information Authority of Japan (GIAJ, 国土地理院):
   <https://www.gsi.go.jp/>, (English) <https://www.gsi.go.jp/ENGLISH/>.
2. _TKY2JGD for Windows Ver.1.3.79_ (reference implementation):
   <https://www.gsi.go.jp/sokuchikijun/tky2jgd_download.html>,
   released under [国土地理院コンテンツ利用規約] which compatible to CC BY 4.0.
3. Other implementation:
   Python <https://github.com/paqira/jgdtrans-py>,
   Java <https://github.com/paqira/jgdtrans-java>,
   JavaScript/TypeScript <https://github.com/paqira/jgdtrans-js>.

[国土地理院コンテンツ利用規約]: https://www.gsi.go.jp/kikakuchousei/kikakuchousei40182.html