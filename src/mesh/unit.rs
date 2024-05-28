/// The mesh unit, or approximate length of cell's edge.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum MeshUnit {
    /// for 1 \[km\]
    One,
    /// for 5 \[km\]
    Five,
}

impl From<&MeshUnit> for u8 {
    #[inline]
    fn from(value: &MeshUnit) -> Self {
        value.to_u8()
    }
}

impl MeshUnit {
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub(crate) const fn to_u8(&self) -> u8 {
        match self {
            Self::One => 1,
            Self::Five => 5,
        }
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for MeshUnit {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u8(self.to_u8())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for MeshUnit {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<MeshUnit, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        match <u8 as serde::Deserialize>::deserialize(deserializer)? {
            1 => Ok(Self::One),
            5 => Ok(Self::Five),
            v => Err(serde::de::Error::custom(format_args!(
                "invalid value: integer `{}`, expected an integer, 1 or 5",
                v,
            ))),
        }
    }
}

#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    #[cfg(feature = "serde")]
    fn test_serde() {
        use serde_test::{assert_tokens, Token};

        assert_tokens(&MeshUnit::One, &[Token::U8(1)]);
        assert_tokens(&MeshUnit::Five, &[Token::U8(5)]);
    }
}
