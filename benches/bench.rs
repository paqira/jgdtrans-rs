#![feature(test)]
/// Notes
/// 1. Every bench has 1,000 transformation
extern crate test;

use std::fs;
use test::Bencher;

use jgdtrans::*;

const OPS: usize = 1000;
const POINTS: [Point; 50] = [
    // 1	北海道	札幌市
    Point::new(43.064310, 141.346879, 0.0),
    // 2	青森県	青森市
    Point::new(40.824589, 140.740548, 0.0),
    // 3	岩手県	盛岡市
    Point::new(39.703526, 141.152696, 0.0),
    // 4	宮城県	仙台市
    Point::new(38.268579, 140.872072, 0.0),
    // 5	秋田県	秋田市
    Point::new(39.718626, 140.102381, 0.0),
    // 6	山形県	山形市
    Point::new(38.240434, 140.363690, 0.0),
    // 7	福島県	福島市
    Point::new(37.750029, 140.467771, 0.0),
    // 8	茨城県	水戸市
    Point::new(36.341737, 140.446824, 0.0),
    // 9	栃木県	宇都宮市
    Point::new(36.565912, 139.883592, 0.0),
    // 10	群馬県	前橋市
    Point::new(36.390688, 139.060453, 0.0),
    // 11	埼玉県	さいたま市
    Point::new(35.857033, 139.649012, 0.0),
    // 12	千葉県	千葉市
    Point::new(35.604560, 140.123154, 0.0),
    // 13	東京都	新宿区
    Point::new(35.689501, 139.691722, 0.0),
    // 14	神奈川県	横浜市
    Point::new(35.447734, 139.642537, 0.0),
    // 15	新潟県	新潟市
    Point::new(37.902451, 139.023245, 0.0),
    // 16	富山県	富山市
    Point::new(36.695265, 137.211305, 0.0),
    // 17	石川県	金沢市
    Point::new(36.594606, 136.625669, 0.0),
    // 18	福井県	福井市
    Point::new(36.065209, 136.221720, 0.0),
    // 19	山梨県	甲府市
    Point::new(35.664108, 138.568455, 0.0),
    // 20	長野県	長野市
    Point::new(36.651306, 138.180904, 0.0),
    // 21	岐阜県	岐阜市
    Point::new(35.391174, 136.723657, 0.0),
    // 22	静岡県	静岡市
    Point::new(34.976944, 138.383056, 0.0),
    // 23	愛知県	名古屋市
    Point::new(35.180209, 136.906582, 0.0),
    // 24	三重県	津市
    Point::new(34.730278, 136.508611, 0.0),
    // 25	滋賀県	大津市
    Point::new(35.004513, 135.868568, 0.0),
    // 26	京都府	京都市
    Point::new(35.021242, 135.755613, 0.0),
    // 27	大阪府	大阪市
    Point::new(34.686344, 135.520037, 0.0),
    // 28	兵庫県	神戸市
    Point::new(34.691257, 135.183078, 0.0),
    // 29	奈良県	奈良市
    Point::new(34.685274, 135.832861, 0.0),
    // 30	和歌山県	和歌山市
    Point::new(34.226111, 135.167500, 0.0),
    // 31	鳥取県	鳥取市
    Point::new(35.503449, 134.238261, 0.0),
    // 32	島根県	松江市
    Point::new(35.472293, 133.050520, 0.0),
    // 33	岡山県	岡山市
    Point::new(34.661739, 133.935032, 0.0),
    // 34	広島県	広島市
    Point::new(34.396558, 132.459646, 0.0),
    // 35	山口県	山口市
    Point::new(34.186041, 131.470654, 0.0),
    // 36	徳島県	徳島市
    Point::new(34.065761, 134.559286, 0.0),
    // 37	香川県	高松市
    Point::new(34.340112, 134.043291, 0.0),
    // 38	愛媛県	松山市
    Point::new(33.841642, 132.765682, 0.0),
    // 39	高知県	高知市
    Point::new(33.559722, 133.531111, 0.0),
    // 40	福岡県	福岡市
    Point::new(33.606389, 130.417968, 0.0),
    // 41	佐賀県	佐賀市
    Point::new(33.249351, 130.298792, 0.0),
    // 42	長崎県	長崎市
    Point::new(32.750040, 129.867251, 0.0),
    // 43	熊本県	熊本市
    Point::new(32.789800, 130.741584, 0.0),
    // 44	大分県	大分市
    Point::new(33.238130, 131.612645, 0.0),
    // 45	宮崎県	宮崎市
    Point::new(31.911034, 131.423887, 0.0),
    // 46	鹿児島県	鹿児島市
    Point::new(31.560171, 130.558025, 0.0),
    // 47	沖縄県	那覇市
    Point::new(26.212445, 127.680922, 0.0),
    //
    // 稚内
    Point::new(45.416008945992424, 141.67311999996528, 0.0),
    // 根室
    Point::new(43.342594304831565, 145.58749639492657, 0.0),
    // 小笠原
    Point::new(27.100098446387364, 142.20099641876226, 0.0),
];

macro_rules! impl_bench {
    ($m:ident, $n:ident) => {
        #[bench]
        fn $m(b: &mut Bencher) {
            let s = fs::read_to_string("benches/SemiDyna2023.par")
                .expect("file not found 'SemiDyna2023.par'");
            let tf = Transformer::from_str(&s, Format::SemiDynaEXE)
                .expect("fail to parse 'SemiDyna2023.par'");

            let ps = POINTS.iter().cycle().take(OPS).collect::<Vec<_>>();

            b.iter(|| {
                let _ = ps.iter().map(|p| tf.$m(p).unwrap()).collect::<Vec<_>>();
            });
        }

        #[bench]
        fn $n(b: &mut Bencher) {
            let s = fs::read_to_string("benches/SemiDyna2023.par")
                .expect("file not found 'SemiDyna2023.par'");
            let tf = Transformer::from_str(&s, Format::SemiDynaEXE)
                .expect("fail to parse 'SemiDyna2023.par'");

            let ps = POINTS.iter().cycle().take(OPS).collect::<Vec<_>>();

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
