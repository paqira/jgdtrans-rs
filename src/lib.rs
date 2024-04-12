//! # jgdtrans
//!
//! Unofficial coordinate transformer by _Gridded Correction Parameter_
//! which Geospatial Information Authority of Japan (GIAJ) distributing [^1].
//!
//! 国土地理院が公開しているパラメータファイル（par ファイル）による座標変換（順逆変換）を提供します [^1]。
//!
//! ```no_run
//! use std::error::Error;
//! use std::fs;
//!
//! use jgdtrans::{Format, Point, Transformer};
//!
//! fn main() -> Result<(), Box<dyn Error>> {
//!     // Deserialize par-formatted file, e.g. SemiDyna2023.par
//!     let s = fs::read_to_string("SemiDyna2023.par").expect("file not found 'SemiDyna2023.par'");
//!     let tf = Transformer::from_par(&s, Format::SemiDynaEXE)?;
//!
//!     // Makes the origin of transformation
//!     let origin = Point::try_new(35.0, 135.0, 2.34)?;
//!     // Prints Origin: Point { latitude: 35.0, longitude: 135.0, altitude: 2.34 }
//!     println!("Origin: {origin:?}");
//!
//!     // Perform forward transformation resulting a Point
//!     let result = tf.forward(&origin)?;
//!     // Prints Forward: Point { latitude: 34.99999831111111, longitude: 135.00000621666666, altitude: 2.33108 }
//!     println!("Forward: {result:?}");
//!
//!     // Perform backward transformation
//!     let p = tf.backward(&result)?;
//!     // Prints Backward: Point { latitude: 34.999999999999986, longitude: 135.0, altitude: 2.339999999105295 }
//!     println!("Backward: {p:?}");
//!
//!     // Perform verified backward transformation
//!     // that the error from the exact solution is less than GIAJ parameter error
//!     let q = tf.backward_safe(&result)?;
//!     // Prints Verified Backward: Point { latitude: 35.0, longitude: 135.0, altitude: 2.3400000000005847 }
//!     println!("Verified Backward: {q:?}");
//!
//!     Ok(())
//! }
//! ```
//!
//! Features:
//!
//! - Supports offline transformation (no web API)
//! - Supports both original forward and backward transformation
//! - Supports verified backward transformation
//! - Supports all [TKY2JGD], [PatchJGD], [PatchJGD(H)], [HyokoRev], [SemiDynaEXE]
//!   and [POS2JGD] (geonetF3 and ITRF2014)
//!   - For example, Tokyo Datum to JGD2000 ([EPSG:4301] to [EPSG:4612])
//!     and JGD2000 to JGD2011 ([EPSG:4612] to [EPSG:6668])
//! - Clean implementation
//! - No dependency
//!   - It depends on [`serde`][serde] and [`serde_repr`][serde_repr] crates only if `serde` feature on
//!
//! [TKY2JGD]: https://www.gsi.go.jp/sokuchikijun/tky2jgd.html
//! [PatchJGD]: https://vldb.gsi.go.jp/sokuchi/surveycalc/patchjgd/index.html
//! [PatchJGD(H)]: https://vldb.gsi.go.jp/sokuchi/surveycalc/patchjgd_h/index.html
//! [HyokoRev]: https://vldb.gsi.go.jp/sokuchi/surveycalc/hyokorev/hyokorev.html
//! [SemiDynaEXE]: https://vldb.gsi.go.jp/sokuchi/surveycalc/semidyna/web/index.html
//! [POS2JGD]: https://positions.gsi.go.jp/cdcs
//!
//! [EPSG:4301]: https://epsg.io/4301
//! [EPSG:4612]: https://epsg.io/4612
//! [EPSG:6668]: https://epsg.io/6668
//!
//! [serde]: https://crates.io/crates/serde
//! [serde_repr]: https://crates.io/crates/serde_repr
//!
//! This package does not contain parameter files, download it from GIAJ [^7].
//!
//! このパッケージはパラメータファイルを提供しません。公式サイトよりダウンロードしてください [^2]。
//!
//! We use _TKY2JGD for Windows Ver.1.3.79_ [^3] as a reference.
//!
//! # Serialization and Deserialization
//!
//! ## Par File
//!
//! We provide API to parse par file, [`Transformer::from_par`] or [`par::from_str`].
//!
//! ```no_run
//! use std::fs;
//! # use std::error::Error;
//! use jgdtrans::{Format, Transformer};
//!
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let s = fs::read_to_string("SemiDyna2023.par").expect("file not found 'SemiDyna2023.par'");
//! let tf = Transformer::from_par(&s, Format::SemiDynaEXE)?;
//! // This is equivalent to:
//! // let tf = jgdtrans::par::from_str(&s, Format::SemiDynaEXE)?;
//! # Ok(())}
//! ```
//!
//! ## Json File
//!
//! It supports (de)serialization by [`serde` crate](https://crates.io/crates/serde)
//! for all `struct` including [`Transformer`] (deserialized object of par-formatted data)
//! only if the feature `serde` is enabled.
//! We show a (de)serialization example to/from json;
//!
//! ```
//! use std::error::Error;
//! use serde_json;
//! use jgdtrans::{
//!     Format,
//!     Parameter,
//!     Transformer,
//!     TransformerBuilder,
//! };
//!
//! fn main() -> serde_json::Result<()> {
//!     // Construct a Transformer by TransformerBuilder
//!     let tf = TransformerBuilder::new(Format::TKY2JGD)
//!         .parameter(12345678, Parameter::new(1., 2., 3.))
//!         .build();
//!
//!     // Serialize to json
//!     let json = serde_json::to_string(&tf)?;
//!     assert_eq!(
//!         json,
//!         r#"{"format":"TKY2JGD","parameter":{"12345678":{"latitude":1.0,"longitude":2.0,"altitude":3.0}}}"#
//!     );
//!
//!     // Deserialize from json
//!     let result: Transformer = serde_json::from_str(&json)?;
//!     assert_eq!(result, tf);
//!
//!     Ok(())
//! }
//! ```
//!
//! [^1]: Geospatial Information Authority of Japan (GIAJ, 国土地理院): <https://www.gsi.go.jp/>
//!       (English) <https://www.gsi.go.jp/ENGLISH/>.
//!
//! [^2]: TKY2JGD: <https://www.gsi.go.jp/sokuchikijun/tky2jgd_download.html>;
//!       PatchJGD, PatchJGD(H) and HyokoRev: <https://www.gsi.go.jp/sokuchikijun/sokuchikijun41012.html>;
//!       SemiDynaEXE: <https://www.gsi.go.jp/sokuchikijun/semidyna.html>;
//!       geonetF3 and ITRF2014 (POS2JGD): <https://positions.gsi.go.jp/cdcs/>.
//!
//! [^3]: TKY2JGD for Windows Ver.1.3.79 (reference implementation):
//!       <https://www.gsi.go.jp/sokuchikijun/tky2jgd_download.html>
//!       released under [国土地理院コンテンツ利用規約](https://www.gsi.go.jp/kikakuchousei/kikakuchousei40182.html)
//!       which compatible to CC BY 4.0.
//!
//! [^4]: Python implementation: <https://github.com/paqira/jgdtrans-py>.
#![feature(float_next_up_down)]

#[doc(inline)]
pub use error::{Error, Result};
#[doc(inline)]
pub use par::Format;
#[doc(inline)]
pub use point::Point;
#[doc(inline)]
pub use transformer::{Parameter, Transformer, TransformerBuilder};

pub mod dms;
pub mod error;
pub mod mesh;
pub mod par;
pub mod point;
pub mod transformer;
