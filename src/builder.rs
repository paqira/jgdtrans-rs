use std::collections::HashMap;
use std::hash::{BuildHasher, RandomState};

use crate::{Format, Parameter, Transformer};

/// The builder of [`Transformer`].
///
/// # Safety
///
/// Panics when `format` is not assigned.
///
/// # Example
///
/// ```
/// # use std::collections::HashMap;
/// # use jgdtrans::*;
/// #
/// // from SemiDynaEXE2023.par
/// let tf: Transformer = TransformerBuilder::new()
///     .format(Format::SemiDynaEXE)
///     .parameters([
///         (54401005, (-0.00622, 0.01516, 0.0946)),
///         (54401055, (-0.0062, 0.01529, 0.08972)),
///     ])
///     .description("My parameter".to_string())
///     .build();
///
/// assert_eq!(tf.format, Format::SemiDynaEXE);
/// assert_eq!(
///     tf.parameter,
///     HashMap::from([
///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
///     ])
/// );
/// assert_eq!(tf.description, Some("My parameter".to_string()));
/// ```
#[derive(Debug, Default)]
pub struct TransformerBuilder<
    #[cfg(not(feature = "serde"))] S = RandomState,
    #[cfg(feature = "serde")] S: Default = RandomState,
> {
    format: Option<Format>,
    parameter: HashMap<u32, Parameter, S>,
    description: Option<String>,
}

impl TransformerBuilder<RandomState> {
    /// Makes a [`TransformerBuilder`].
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use jgdtrans::*;
    /// #
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .build();
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(tf.parameter, HashMap::new());
    /// assert_eq!(tf.description, None);
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::with_hasher(RandomState::new())
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> TransformerBuilder<S> {
    /// Makes a [`TransformerBuilder`] which uses the given hash builder to hash meshcode.
    ///
    /// See [`HashMap::with_hasher`] for detail.
    #[inline]
    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            format: None,
            parameter: HashMap::with_hasher(hash_builder),
            description: None,
        }
    }

    /// Updates by a [`Format`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// #
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .build();
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// ```
    #[inline]
    pub const fn format(mut self, format: Format) -> Self {
        self.format = Some(format);
        self
    }

    /// Updates [`description`](Transformer::description).
    ///
    /// ```
    /// # use jgdtrans::*;
    /// #
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .description("My parameter".to_string())
    ///     .build();
    ///
    /// assert_eq!(tf.description, Some("My parameter".to_string()));
    /// ```
    #[inline]
    pub fn description(mut self, s: String) -> Self {
        self.description = Some(s);
        self
    }

    /// Builds [`Transformer`].
    ///
    /// # Safety
    ///
    /// Panics when `format` is not assigned.
    #[inline]
    pub fn build(self) -> Transformer<S> {
        Transformer {
            format: self.format.expect("format is not assigned"),
            parameter: self.parameter,
            description: self.description,
        }
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> TransformerBuilder<S>
where
    S: BuildHasher,
{
    /// Adds a [`Parameter`].
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .parameter(54401005, (-0.00622, 0.01516, 0.0946))
    ///     .build();
    ///
    /// assert_eq!(
    ///     tf.parameter,
    ///     HashMap::from([(54401005, Parameter::new(-0.00622, 0.01516, 0.0946)), ])
    /// );
    /// ```
    #[inline]
    pub fn parameter(mut self, meshcode: u32, parameter: impl Into<Parameter>) -> Self {
        self.parameter.insert(meshcode, parameter.into());
        self
    }

    /// Adds [`Parameter`]s.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .parameters([
    ///         (54401005, (-0.00622, 0.01516, 0.0946)),
    ///         (54401055, (-0.0062, 0.01529, 0.08972)),
    ///         (54401100, (-0.00663, 0.01492, 0.10374)),
    ///         (54401150, (-0.00664, 0.01506, 0.10087)),
    ///     ])
    ///     .build();
    ///
    /// assert_eq!(
    ///     tf.parameter,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    /// ```
    #[inline]
    pub fn parameters(
        mut self,
        parameters: impl IntoIterator<Item = (u32, impl Into<Parameter>)>,
    ) -> Self {
        for (meshcode, parameter) in parameters.into_iter() {
            self.parameter.insert(meshcode, parameter.into());
        }
        self
    }

    /// Shrinks the capacity of the [`HashMap`] of the parameter as much as possible.
    ///
    /// See [`HashMap::shrink_to_fit`] for detail.
    #[inline]
    pub fn shrink_to_fit(mut self) -> Self {
        self.parameter.shrink_to_fit();
        self
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Clone
    for TransformerBuilder<S>
where
    S: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            format: self.format.clone(),
            parameter: self.parameter.clone(),
            description: self.description.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.format.clone_from(&source.format);
        self.parameter.clone_from(&source.parameter);
        self.description.clone_from(&source.description);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic(expected = "format is not assigned")]
    fn test_panic() {
        let _ = TransformerBuilder::new().build();
    }

    #[test]
    fn test_impl() {
        let tf = TransformerBuilder::new()
            .format(Format::SemiDynaEXE)
            .parameter(54401005, (-0.00622, 0.01516, 0.0946))
            .parameter(54401055, [-0.0062, 0.01529, 0.08972])
            .parameter(54401100, Parameter::new(-0.00663, 0.01492, 0.10374))
            .build();

        assert_eq!(
            tf.parameter,
            [
                (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
                (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
                (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
            ]
            .into()
        );
    }
}
