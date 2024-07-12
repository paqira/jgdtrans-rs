use crate::mesh::{MeshCoord, MeshNode, MeshUnit};
use crate::vector::f64x2;
use crate::Point;

/// Represents unit mesh cell, a quadruplet of [`MeshNode`]s and [`MeshUnit`].
///
/// This has no other [`MeshNode`]s inside `self` in the unit.
///
/// The cell is, roughly, a square with `mesh_unit` \[km\] length edges.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// #
/// # fn wrapper() -> Option<()> {
/// // Construct from latitude and longitude, altitude ignores
/// // (The result depends on the mesh unit)
/// let point = Point::new_unchecked(36.10377479, 140.087855041, 0.0);
/// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
/// assert_eq!(cell.south_west(), &MeshNode::try_from_meshcode(&54401027)?);
/// assert_eq!(cell.south_east(), &MeshNode::try_from_meshcode(&54401028)?);
/// assert_eq!(cell.north_west(), &MeshNode::try_from_meshcode(&54401037)?);
/// assert_eq!(cell.north_east(), &MeshNode::try_from_meshcode(&54401038)?);
///
/// // Construct from node
/// let node = MeshNode::try_from_meshcode(&54401027)?;
/// assert_eq!(MeshCell::try_from_node(node, MeshUnit::One)?, cell);
///
/// // Construct from meshcode
/// assert_eq!(MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?, cell);
///
/// // Find the position within the cell, from 0.0 to 1.0
/// // (Again, the result depends on the mesh unit)
/// let (latitude, longitude) = cell.position(&point);
/// assert_eq!(latitude, 0.4529748000001632);
/// assert_eq!(longitude, 0.028403280000475206);
///
/// // the south-west node of the cell is (0, 0), origin
/// let (latitude, longitude) = cell.position(&cell.south_west().to_point());
/// assert!((0.0 - latitude).abs() < 1e-12);
/// assert!((0.0 - longitude).abs() < 1e-12);
///
/// // the north-east node is (1, 1)
/// let (latitude, longitude) = cell.position(&cell.north_east().to_point());
/// assert!((1.0 - latitude).abs() < 1e-12);
/// assert!((1.0 - longitude).abs() < 1e-12);
/// # Some(())}
/// # fn main() {wrapper();()}
/// ```
#[derive(Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MeshCell {
    /// The south-west node of the cell
    pub(crate) south_west: MeshNode,
    /// The south-east node of the cell
    pub(crate) south_east: MeshNode,
    /// The north-west node of the cell
    pub(crate) north_west: MeshNode,
    /// The north-east node of the cell
    pub(crate) north_east: MeshNode,
    /// The mesh unit which is consistent with nodes
    pub(crate) mesh_unit: MeshUnit,
}

impl MeshCell {
    /// Makes a [`MeshCell`].
    ///
    /// # Errors
    ///
    /// Returns [`None`] when the nodes and `mesh_unit` does not
    /// construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.south_west(), &MeshNode::try_from_meshcode(&54401027)?);
    /// assert_eq!(cell.south_east(), &MeshNode::try_from_meshcode(&54401028)?);
    /// assert_eq!(cell.north_west(), &MeshNode::try_from_meshcode(&54401037)?);
    /// assert_eq!(cell.north_east(), &MeshNode::try_from_meshcode(&54401038)?);
    /// assert_eq!(cell.mesh_unit(), &MeshUnit::One);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    pub const fn new(
        south_west: MeshNode,
        south_east: MeshNode,
        north_west: MeshNode,
        north_east: MeshNode,
        mesh_unit: MeshUnit,
    ) -> Option<Self> {
        // consistently on unit v.s. the third
        if !south_west.is_mesh_unit(&mesh_unit)
            || !south_east.is_mesh_unit(&mesh_unit)
            || !north_west.is_mesh_unit(&mesh_unit)
            || !north_east.is_mesh_unit(&mesh_unit)
        {
            return None;
        };

        // TODO: use `?` when `feature(const_trait_impl)` stable
        let lat_next = match south_west.latitude.next_up(&mesh_unit) {
            Some(r) => r,
            None => return None,
        };
        let lng_next = match south_west.longitude.next_up(&mesh_unit) {
            Some(r) => r,
            None => return None,
        };

        // TODO: use Ord::ne when `feature(const_trait_impl)` stable
        macro_rules! ne {
            ($left:expr, $right:expr) => {
                $left.first != $right.first
                    || $left.second != $right.second
                    || $left.third != $right.third
            };
        }

        if ne!(lat_next, north_west.latitude)
            || ne!(south_west.longitude, north_west.longitude)
            || ne!(south_west.latitude, south_east.latitude)
            || ne!(lng_next, south_east.longitude)
            || ne!(lat_next, north_east.latitude)
            || ne!(lng_next, north_east.longitude)
        {
            return None;
        }

        Some(Self {
            south_west,
            south_east,
            north_west,
            north_east,
            mesh_unit,
        })
    }

    /// Returns the south-west node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.south_west(), &MeshNode::try_from_meshcode(&54401027)?);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn south_west(&self) -> &MeshNode {
        &self.south_west
    }

    /// Returns the south-east node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.south_east(), &MeshNode::try_from_meshcode(&54401028)?);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn south_east(&self) -> &MeshNode {
        &self.south_east
    }

    /// Returns the north-west node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.north_west(), &MeshNode::try_from_meshcode(&54401037)?);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn north_west(&self) -> &MeshNode {
        &self.north_west
    }

    /// Returns the north-east node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.north_east(), &MeshNode::try_from_meshcode(&54401038)?);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn north_east(&self) -> &MeshNode {
        &self.north_east
    }

    /// Returns the mesh unit of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.mesh_unit(), &MeshUnit::One);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn mesh_unit(&self) -> &MeshUnit {
        &self.mesh_unit
    }

    /// Makes a [`MeshCell`] with the south-east [`MeshNode`] which represented by meshcode `code`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when an invalid `meshcode` given,
    /// or it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// assert_eq!(
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?,
    ///     MeshCell::new(
    ///         MeshNode::try_from_meshcode(&54401027)?,
    ///         MeshNode::try_from_meshcode(&54401028)?,
    ///         MeshNode::try_from_meshcode(&54401037)?,
    ///         MeshNode::try_from_meshcode(&54401038)?,
    ///         MeshUnit::One
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn try_from_meshcode(meshcode: &u32, mesh_unit: MeshUnit) -> Option<Self> {
        match MeshNode::try_from_meshcode(meshcode) {
            Some(r) => Self::try_from_node(r, mesh_unit),
            None => None,
        }
    }

    /// Makes a [`MeshCell`] that has `node` as a south-west node.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    ///
    /// assert_eq!(
    ///     MeshCell::try_from_node(south_west, MeshUnit::One)?,
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    pub const fn try_from_node(node: MeshNode, mesh_unit: MeshUnit) -> Option<Self> {
        // TODO: use `?` when `feature(const_trait_impl)` stable
        let Some(next_lat_coord) = node.latitude.next_up(&mesh_unit) else {
            return None;
        };
        let Some(next_lng_coord) = node.longitude.next_up(&mesh_unit) else {
            return None;
        };

        // TODO: use Clone::clone when `feature(const_trait_impl)` stable
        macro_rules! clone {
            ($src:expr) => {
                MeshCoord {
                    first: $src.first,
                    second: $src.second,
                    third: $src.third,
                }
            };
        }

        // Call MeshNode::try_new
        // to check next_coord_lat
        // TODO: use `?` when `feature(const_trait_impl)` stable
        let Some(south_east) = MeshNode::new(clone!(node.latitude), clone!(next_lng_coord)) else {
            return None;
        };
        let Some(north_west) = MeshNode::new(clone!(next_lat_coord), clone!(node.longitude)) else {
            return None;
        };
        let Some(north_east) = MeshNode::new(clone!(next_lat_coord), clone!(next_lng_coord)) else {
            return None;
        };

        Some(Self {
            south_west: node,
            south_east,
            north_west,
            north_east,
            mesh_unit,
        })
    }

    /// Makes a [`MeshCell`] which contains a [`Point`].
    ///
    /// The result is independent on [`point.altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// Returns [`None`] when it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let point: Point = Point::new_unchecked(36.10377479, 140.087855041, 0.0);
    ///
    /// assert_eq!(
    ///     MeshCell::try_from_point(&point, MeshUnit::One)?,
    ///     MeshCell::new(
    ///         MeshNode::try_from_meshcode(&54401027)?,
    ///         MeshNode::try_from_meshcode(&54401028)?,
    ///         MeshNode::try_from_meshcode(&54401037)?,
    ///         MeshNode::try_from_meshcode(&54401038)?,
    ///         MeshUnit::One
    ///     )?
    /// );
    ///
    /// assert_eq!(
    ///     MeshCell::try_from_point(&point, MeshUnit::Five)?,
    ///     MeshCell::new(
    ///         MeshNode::try_from_meshcode(&54401005)?,
    ///         MeshNode::try_from_meshcode(&54401100)?,
    ///         MeshNode::try_from_meshcode(&54401055)?,
    ///         MeshNode::try_from_meshcode(&54401150)?,
    ///         MeshUnit::Five
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn try_from_point(point: &Point, mesh_unit: MeshUnit) -> Option<Self> {
        MeshNode::try_from_point(point, &mesh_unit)
            .and_then(|node| Self::try_from_node(node, mesh_unit))
    }

    /// Return the position in the cell.
    ///
    /// This returns from 0.0 to 1.0 for each latitude and longitude
    /// if `point` is inside `self`.
    ///
    /// We note that the result is a (𝑙𝑎𝑡𝑖𝑡𝑢𝑑𝑒, 𝑙𝑜𝑛𝑔𝑖𝑡𝑢𝑑𝑒) pair,
    /// not a right-handed (𝑦, 𝑥) pair.
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// // sample latitude and longitude
    /// let point = Point::new_unchecked(36.10377479, 140.087855041, 0.0);
    ///
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
    ///
    /// // the south-west of the cell is (0, 0), origin
    /// let (latitude, longitude) = cell.position(&cell.south_west().to_point());
    /// assert!((0.0 - latitude).abs() < 1e-12);
    /// assert!((0.0 - longitude).abs() < 1e-12);
    ///
    /// // the south-east is (0, 1)
    /// let (latitude, longitude) = cell.position(&cell.south_east().to_point());
    /// assert!((0.0 - latitude).abs() < 1e-12);
    /// assert!((1.0 - longitude).abs() < 1e-12);
    ///
    /// // the north-west is (1, 0)
    /// let (latitude, longitude) = cell.position(&cell.north_west().to_point());
    /// assert!((1.0 - latitude).abs() < 1e-12);
    /// assert!((0.0 - longitude).abs() < 1e-12);
    ///
    /// // the north-east is (1, 1)
    /// let (latitude, longitude) = cell.position(&cell.north_east().to_point());
    /// assert!((1.0 - latitude).abs() < 1e-12);
    /// assert!((1.0 - longitude).abs() < 1e-12);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let point = Point::new_unchecked(36.10377479, 140.087855041, 0.0);
    ///
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
    /// assert_eq!(
    ///     cell.position(&point),
    ///     (0.4529748000001632, 0.028403280000475206)
    /// );
    ///
    /// // the result depends on the mesh unit
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::Five)?;
    /// assert_eq!(
    ///     cell.position(&point),
    ///     (0.4905949600000099, 0.405680656000186)
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn position(&self, point: &Point) -> (f64, f64) {
        let pos = f64x2!(point.latitude, point.longitude)
            - f64x2!(
                self.south_west.latitude.to_latitude(),
                self.south_west.longitude.to_longitude()
            );

        match self.mesh_unit {
            MeshUnit::One => f64x2!(120., 80.) * pos,
            MeshUnit::Five => f64x2!(24., 16.) * pos,
        }
        .into()
    }
}

impl Clone for MeshCell {
    fn clone(&self) -> Self {
        Self {
            south_west: self.south_west.clone(),
            south_east: self.south_east.clone(),
            north_west: self.north_west.clone(),
            north_east: self.north_east.clone(),
            mesh_unit: self.mesh_unit,
        }
    }
    
    fn clone_from(&mut self, source: &Self) {
        self.south_west = source.south_west.clone();
        self.south_east = source.south_east.clone();
        self.north_west = source.north_west.clone();
        self.north_east = source.north_east.clone();
        self.mesh_unit = source.mesh_unit;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_try_new() {
        // healty
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::One,
        )
        .is_some());
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401005).unwrap(),
            MeshNode::try_from_meshcode(&54401100).unwrap(),
            MeshNode::try_from_meshcode(&54401055).unwrap(),
            MeshNode::try_from_meshcode(&54401150).unwrap(),
            MeshUnit::Five,
        )
        .is_some());

        // error
        // incorrect unit
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::Five,
        )
        .is_none());
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401005).unwrap(),
            MeshNode::try_from_meshcode(&54401100).unwrap(),
            MeshNode::try_from_meshcode(&54401055).unwrap(),
            MeshNode::try_from_meshcode(&54401150).unwrap(),
            MeshUnit::One,
        )
        .is_none());

        // not a unit cell
        // longitude
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::One,
        )
        .is_none());
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401036).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::One,
        )
        .is_none());
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshUnit::One,
        )
        .is_none());

        // latitude
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401018).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::One,
        )
        .is_none());
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::One,
        )
        .is_none());
        assert!(MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshUnit::One,
        )
        .is_none());
    }

    #[test]
    fn test_getter() {
        let cell = MeshCell::new(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshNode::try_from_meshcode(&54401028).unwrap(),
            MeshNode::try_from_meshcode(&54401037).unwrap(),
            MeshNode::try_from_meshcode(&54401038).unwrap(),
            MeshUnit::One,
        )
        .unwrap();

        assert_eq!(
            cell.south_west(),
            &MeshNode::try_from_meshcode(&54401027).unwrap()
        );
        assert_eq!(
            cell.south_east(),
            &MeshNode::try_from_meshcode(&54401028).unwrap()
        );
        assert_eq!(
            cell.north_west(),
            &MeshNode::try_from_meshcode(&54401037).unwrap()
        );
        assert_eq!(
            cell.north_east(),
            &MeshNode::try_from_meshcode(&54401038).unwrap()
        );
        assert_eq!(cell.mesh_unit(), &MeshUnit::One);
    }

    #[test]
    fn test_try_from_meshcode() {
        assert_eq!(
            MeshCell::try_from_meshcode(&54401027, MeshUnit::One).unwrap(),
            MeshCell::new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One,
            )
            .unwrap()
        );
        assert_eq!(
            MeshCell::try_from_meshcode(&54401005, MeshUnit::Five).unwrap(),
            MeshCell::new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::Five,
            )
            .unwrap()
        );

        // error
        assert!(MeshCell::try_from_meshcode(&54401027, MeshUnit::Five).is_none());
    }

    #[test]
    fn test_try_from_sw_node() {
        assert_eq!(
            MeshCell::try_from_node(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshUnit::One,
            )
            .unwrap(),
            MeshCell::new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One,
            )
            .unwrap()
        );
        assert_eq!(
            MeshCell::try_from_node(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshUnit::Five,
            )
            .unwrap(),
            MeshCell::new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::Five,
            )
            .unwrap()
        );

        // error
        assert!(MeshCell::try_from_node(
            MeshNode::try_from_meshcode(&54401027).unwrap(),
            MeshUnit::Five,
        )
        .is_none());
    }

    #[test]
    fn test_try_from_point() {
        let point = Point::new_unchecked(36.10377479, 140.087855041, 10.0);

        assert_eq!(
            MeshCell::try_from_point(&point, MeshUnit::One).unwrap(),
            MeshCell::new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One,
            )
            .unwrap()
        );
        assert_eq!(
            MeshCell::try_from_point(&point, MeshUnit::Five).unwrap(),
            MeshCell::new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::Five,
            )
            .unwrap()
        );
    }

    #[test]
    fn test_position() {
        let point = Point::new_unchecked(36.10377479, 140.087855041, 10.0);

        let cell = MeshCell::try_from_point(&point, MeshUnit::One).unwrap();
        assert_eq!(
            cell.position(&point),
            (0.4529748000001632, 0.028403280000475206)
        );

        let cell = MeshCell::try_from_point(&point, MeshUnit::Five).unwrap();
        assert_eq!(
            cell.position(&point),
            (0.4905949600000099, 0.405680656000186)
        );
    }
}
