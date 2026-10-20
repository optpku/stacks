module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ResidualConstruction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints

/-! # The concrete reduced point closure in the quasi-separated source range

Its reduced atlas is the direct public owner. Its decency certificate
contains the explicitly descended equalizer-field point. No broad
unconditional point-closure integrality instance is introduced.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.PointClosure

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/-- The image in `X` of a point of the reduced closure of `x`. -/
def pointMap (z : Points (space x)) : closedSubset x :=
  ⟨Points.map (ι x) z, by
    change Points.map (ι x) z ∈ (closedSubset x : Set (Points X))
    rw [← range_ι x]
    exact Set.mem_range_self z⟩

/-- The map from points of the reduced closure to its closed-subset points is bijective. -/
theorem pointMap_bijective : Function.Bijective (pointMap x) := by
  sorry

/-- A field-valued point supported on the closed subset lies in the relative
image sheaf of its reduced atlas. This asserts membership of the specified
section; it does not choose a factorization morphism. -/
theorem representative_range (z : closedSubset x) :
    Subfunctor.range (Quotient.out z.val : FieldValuedPoint X).hom ≤
      (Subfunctor.range (ReducedClosed.AtlasImage.chartMap X (closedSubset x))).sheafify
        (Scheme.fppfTopology.over S) := by
  sorry

/-- Retain the representative field and base map, and attach the image
membership proof to its existing sections. -/
def liftRepresentative (z : closedSubset x) : FieldValuedPoint (space x) :=
  FieldValuedPoint.of
    (Quotient.out z.val : FieldValuedPoint X).K
    (Quotient.out z.val : FieldValuedPoint X).structureHom
    (Subfunctor.lift (Quotient.out z.val : FieldValuedPoint X).hom
      (representative_range x z))

/-- The inverse on points is the class of the explicit image-subtype lift. -/
def pointInverse (z : closedSubset x) : Points (space x) :=
  Points.mk (liftRepresentative x z)

/-- The explicit lift is a left inverse to the map on points. -/
theorem pointInverse_pointMap (z : Points (space x)) :
    pointInverse x (pointMap x z) = z := by sorry

/-- The point map is a right inverse to the explicit lift. -/
theorem pointMap_pointInverse (z : closedSubset x) :
    pointMap x (pointInverse x z) = z := by sorry

/-- The point map and its explicit inverse form an equivalence. -/
def pointEquiv : Points (space x) ≃ closedSubset x where
  toFun := pointMap x
  invFun := pointInverse x
  left_inv := pointInverse_pointMap x
  right_inv := pointMap_pointInverse x

/-- The original point viewed in the reduced closure. -/
def originalPoint : closedSubset x := ⟨x, subset_closure (Set.mem_singleton x)⟩

/-- The generic point of the reduced closure corresponding to the original point. -/
def generic : Points (space x) := (pointEquiv x).symm (originalPoint x)

/-- The image of the generic point is the original point. -/
theorem generic_maps_to_original : Points.map (ι x) (generic x) = x :=
  congrArg Subtype.val ((pointEquiv x).apply_symm_apply (originalPoint x))

/-- The generic point belongs to the generic-point set of the reduced closure. -/
theorem generic_mem : generic x ∈ AlgebraicSpace.genericPoints (space x) := by sorry

/-- The reduced closure of a point is irreducible. -/
instance irreducible : AlgebraicSpace.IsIrreducible (space x) := by sorry

/-- The reduced closure is quasi-separated when the ambient space is. -/
instance quasiSeparated [AlgebraicSpace.IsQuasiSeparated X] :
    AlgebraicSpace.IsQuasiSeparated (space x) := by sorry

/-- The reduced closure is decent when the ambient space is quasi-separated. -/
instance decent [AlgebraicSpace.IsQuasiSeparated X] : AlgebraicSpace.IsDecent (space x) := by
  exact ResidualPoint.decent (space x)

/-- The reduced closure is integral when the ambient space is quasi-separated. -/
instance integral [AlgebraicSpace.IsQuasiSeparated X] : AlgebraicSpace.IsIntegral (space x) where
  toIsReduced := instIsReduced_space x
  toIsDecent := decent x
  toIsIrreducible := irreducible x

end AlgebraicGeometry.AlgebraicSpace.PointClosure
