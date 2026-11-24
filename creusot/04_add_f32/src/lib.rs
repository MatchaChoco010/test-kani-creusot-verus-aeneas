use creusot_std as _;

pub fn add_f32(a: f32, b: f32) -> f32 {
    a + b
}

// 書けない: NaN / ±∞ の条件を仕様に書くには f32::is_finite / f32::is_nan が要るが、creusot-std はこれらに仕様を与えておらず、
// 仕様の中では "called program function `core::f32::<impl f32>::is_finite` in logic context" でコンパイルできない。
// プログラムの中で呼んでも "calling external function `is_finite` with no contract will yield an impossible precondition" となり検証できない
// #[requires(a.is_finite() && b.is_finite())]
// #[ensures(!result.is_nan())]
// pub fn add_not_nan(a: f32, b: f32) -> f32 {
//     a + b
// }

// 検証失敗: 整数値の f32 定数は f64 の最短 10 進表記で Why3 に出力されるため、
// 3.4028235e38 などが Float32 で正確に表せないリテラルとなり Why3 に拒否される
// const MAX: f32 = 3.4028235e38;
// const NEG_MAX: f32 = -3.4028235e38;
// const HALF_MAX: f32 = 1.7014117e38;
// const NEG_HALF_MAX: f32 = -1.7014117e38;
//
// #[requires(NEG_HALF_MAX <= a && a <= HALF_MAX)]
// #[requires(NEG_HALF_MAX <= b && b <= HALF_MAX)]
// #[ensures(NEG_MAX <= result && result <= MAX)]
// pub fn add_finite(a: f32, b: f32) -> f32 {
//     a + b
// }

// 書けない: 丸め (結果は実数の和に最も近い f32) を述べるには f32 の実数値が要るが、
// creusot-std は f32 のビュー (@) も仕様用の f32 の演算も提供しておらず "Cannot take the view of `f32`" でコンパイルできない
// #[ensures(forall<f: f32>
//     (result@ - (a@ + b@)) * (result@ - (a@ + b@)) <= (f@ - (a@ + b@)) * (f@ - (a@ + b@)))]
// pub fn add_rounded(a: f32, b: f32) -> f32 {
//     a + b
// }
