//! # jgdtrans
//!
//! Unofficial coordinate transformer by _Gridded Correction Parameter_
//! which Geospatial Information Authority of Japan (GIAJ) distributing [^1].
//!
//! <span lang="ja">国土地理院が公開しているパラメータファイル（par ファイル）による座標変換（順逆変換）を提供します [^1]。</span>
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
//!     let tf = Transformer::from_str(&s, Format::SemiDynaEXE)?;
//!
//!     // Makes the origin of transformation
//!     let origin = Point::new_unchecked(35.0, 135.0, 2.34);
//!     // Prints Point { latitude: 35.0, longitude: 135.0, altitude: 2.34 }
//!     println!("{origin:?}");
//!
//!     // Perform forward transformation resulting a Point
//!     let result = tf.forward(&origin)?;
//!     // Prints Point { latitude: 34.99999831111111, longitude: 135.00000621666666, altitude: 2.33108 }
//!     println!("{result:?}");
//!
//!     // Perform backward transformation
//!     let p = tf.backward(&result)?;
//!     // Prints Point { latitude: 35.0, longitude: 135.0, altitude: 2.34 }
//!     println!("{p:?}");
//!
//!     // Perform backward transformation compatible to the GIAJ web app/APIs
//!     let q = tf.backward_compat(&result)?;
//!     // Prints Point { latitude: 34.999999999999986, longitude: 135.0, altitude: 2.339999999105295 }
//!     println!("{q:?}");
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
//! This package does not contain parameter files, download it from GIAJ [^2].
//!
//! <span lang="ja">このパッケージはパラメータファイルを提供しません。公式サイトよりダウンロードしてください [^2]。</span>
//!
//! We use _TKY2JGD for Windows Ver.1.3.79_ [^3] as a reference.
//!
//! ## Optional Features
//!
//! - `serde`: supports serialization/deserialization by [`serde` crate][serde],
//!   this requires dependency on [`serde`][serde].
//!
//! [serde]: https://crates.io/crates/serde
//! [fma]: https://en.wikipedia.org/wiki/Multiply–accumulate_operation
//!
//! ## Serialization and Deserialization
//!
//! ### Par (Gridded Correction Parameter)
//!
//! We provide APIs, [`ParData::from_str`].
//!
//! ```no_run
//! use std::error::Error;
//! # use std::fs;
//!
//! use jgdtrans::{Format, ParData};
//!
//! # fn main() -> Result<(), Box<dyn Error>> {
//! let s = fs::read_to_string("SemiDyna2023.par").expect("file not found 'SemiDyna2023.par'");
//! let data = ParData::from_str(&s, Format::SemiDynaEXE)?;
//! # Ok(())}
//! ```
//!
//! ### Json
//!
//! It supports (de)serialization by [`serde` crate][serde]
//! for all `struct` including [`Transformer`] (deserialized object of par-formatted data)
//! only when the feature `serde` is enabled.
//! We show a (de)serialization example to/from json;
//!
//! ```
//! use std::collections::HashMap;
//!
//! use serde_json;
//!
//! use jgdtrans::{
//!     Format,
//!     Parameter,
//!     ParData,
//! };
//!
//! fn main() -> serde_json::Result<()> {
//!     let data = ParData::new(
//!         Format::TKY2JGD,
//!         HashMap::from([(12345678, Parameter::new(1., 2., 3.))])
//!     );
//!
//!     // Serialize to json
//!     let json = serde_json::to_string(&data)?;
//!     assert_eq!(
//!         json,
//!         r#"{"format":"TKY2JGD","parameter":{"12345678":{"latitude":1.0,"longitude":2.0,"altitude":3.0}}}"#
//!     );
//!
//!     // Deserialize from json
//!     let result: ParData = serde_json::from_str(&json)?;
//!     assert_eq!(result.format, Format::TKY2JGD);
//!     assert_eq!(result.parameter, HashMap::from([(12345678, Parameter::new(1., 2., 3.)), ]));
//!     assert_eq!(result.description, None);
//!     Ok(())
//! }
//! ```
//!
//! [^1]: Geospatial Information Authority of Japan (GIAJ, <span lang="ja">国土地理院</span>):
//!       <https://www.gsi.go.jp/>, (English) <https://www.gsi.go.jp/ENGLISH/>.
//!
//! [^2]: TKY2JGD: <https://www.gsi.go.jp/sokuchikijun/tky2jgd_download.html>;
//!       PatchJGD, PatchJGD(H) and HyokoRev: <https://www.gsi.go.jp/sokuchikijun/sokuchikijun41012.html>;
//!       SemiDynaEXE: <https://www.gsi.go.jp/sokuchikijun/semidyna.html>;
//!       geonetF3 and ITRF2014 (POS2JGD): <https://positions.gsi.go.jp/cdcs/>.
//!
//! [^3]: TKY2JGD for Windows Ver.1.3.79 (reference implementation):
//!       <https://www.gsi.go.jp/sokuchikijun/tky2jgd_download.html>
//!       released under [<span lang="ja">国土地理院コンテンツ利用規約</span>][国土地理院コンテンツ利用規約]
//!       which compatible to CC BY 4.0.
//!
//! [^4]: Other implementation:
//!       Python <https://github.com/paqira/jgdtrans-py>,
//!       Java <https://github.com/paqira/jgdtrans-java>,
//!       JavaScript/TypeScript <https://github.com/paqira/jgdtrans-js>.
//!
//! [国土地理院コンテンツ利用規約]: https://www.gsi.go.jp/kikakuchousei/kikakuchousei40182.html
#[doc(inline)]
pub use builder::TransformerBuilder;
#[doc(inline)]
pub use mesh::MeshUnit;
#[doc(inline)]
pub use par::{Format, ParData, ParParser, ParseParError, ParseParErrorKind};
#[doc(inline)]
pub use point::Point;
#[doc(inline)]
pub use trans::{TransformError, TransformErrorKind};
#[doc(inline)]
pub use transformer::{
    Correction, Parameter, ParameterData, ParameterSet, StatisticData, Statistics, Transformer,
};

mod builder;
pub mod dms;
pub mod mesh;
mod par;
mod point;
mod trans;
mod transformer;

// Utility
#[inline(always)]
pub(crate) fn fma(a: f64, b: f64, c: f64) -> f64 {
    if cfg!(target_feature = "fma") {
        a.mul_add(b, c)
    } else {
        a * b + c
    }
}
