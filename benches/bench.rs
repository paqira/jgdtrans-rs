#![feature(test)]
/// Notes
/// 1. Every bench has 1,000 transformation
/// 2. This is *unrealistic*
///    because the parameters (`HashMap` length) are only 4
///    but the real world example has ~10,000 length.

extern crate test;

use test::Bencher;

use jgdtrans::{Format, Point, TransformerBuilder};

#[allow(non_upper_case_globals)]
pub(crate) const SemiDynaEXE: [(u32, (f64, f64, f64)); 4] = [
    (54401005, (-0.00622, 0.01516, 0.0946)),
    (54401055, (-0.0062, 0.01529, 0.08972)),
    (54401100, (-0.00663, 0.01492, 0.10374)),
    (54401150, (-0.00664, 0.01506, 0.10087)),
];

const REPEAT: usize = 500;
const POINTS: [Point; 20] = [
    Point::new(36.094300113821326, 140.08618335887599, 0.0),
    Point::new(36.10601022345694, 140.0858382988577, 0.0),
    Point::new(36.110699535939986, 140.0861474161733, 0.0),
    Point::new(36.11189729717287, 140.0969917730152, 0.0),
    Point::new(36.10932530114988, 140.09674659869518, 0.0),
    Point::new(36.11033220185368, 140.08263157834776, 0.0),
    Point::new(36.10940217693624, 140.1124596662795, 0.0),
    Point::new(36.11179262787281, 140.1065246807473, 0.0),
    Point::new(36.09733885531439, 140.1049095727508, 0.0),
    Point::new(36.10805893617587, 140.07668238220046, 0.0),
    Point::new(36.09610836459087, 140.1047109983162, 0.0),
    Point::new(36.1033308811569, 140.0857622985018, 0.0),
    Point::new(36.11066644178801, 140.0752943599073, 0.0),
    Point::new(36.10259048520414, 140.09543240961895, 0.0),
    Point::new(36.11432747180366, 140.08933355674375, 0.0),
    Point::new(36.10987751663063, 140.10316426055456, 0.0),
    Point::new(36.09638692576236, 140.10377889034723, 0.0),
    Point::new(36.108877456849335, 140.07917661393057, 0.0),
    Point::new(36.09727971736412, 140.09353140946337, 0.0),
    Point::new(36.10737646556959, 140.11191130796195, 0.0),
];

macro_rules! impl_bench {
    ($m:ident, $n:ident) => {
        #[bench]
        fn $m(b: &mut Bencher) {
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let mut ps = Vec::with_capacity(POINTS.len() * REPEAT);
            for _ in 0..REPEAT {
                ps.extend(POINTS);
            }

            b.iter(|| {
                let _ = ps.iter().map(|p| tf.$m(p).unwrap()).collect::<Vec<_>>();
            });
        }

        #[bench]
        fn $n(b: &mut Bencher) {
            let tf =
                TransformerBuilder::with_hasher(hashbrown::hash_map::DefaultHashBuilder::default())
                    .format(Format::SemiDynaEXE)
                    .parameters(SemiDynaEXE)
                    .build();

            let mut ps = Vec::with_capacity(POINTS.len() * REPEAT);
            for _ in 0..REPEAT {
                ps.extend(POINTS);
            }

            b.iter(|| {
                let _ = ps.iter().map(|p| tf.$m(p).unwrap()).collect::<Vec<_>>();
            });
        }
    };
}

impl_bench!(forward_corr, forward_corr_fast_hash);
impl_bench!(backward_corr, backward_corr_fast_hash);
impl_bench!(unchecked_forward_corr, unchecked_forward_corr_fast_hash);
impl_bench!(unchecked_backward_corr, unchecked_backward_corr_fast_hash);
