module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedFibres
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced

/-!
# Geometrically reduced and connected families of curves of dimension one

Reducedness, connectedness, and dimension one of geometric fibres define a
property represented by an open of the base under cartesian morphisms of families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with reduced, connected geometric
fibres of dimension one. -/
def geometricallyReducedConnectedDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    Hom.HasReducedGeometricFibres (hom P) ∧
      AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (hom P) ∧
        ∀ ybar : GeometricPoint (ofOver (base P)),
          dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1

/-- Membership in `geometricallyReducedConnectedDim1` means the geometric fibres
of the structure morphism are reduced, connected, and of dimension one. -/
theorem geometricallyReducedConnectedDim1_iff {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1 S P ↔
      Hom.HasReducedGeometricFibres (hom P) ∧
        AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (hom P) ∧
          ∀ ybar : GeometricPoint (ofOver (base P)),
            dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1 := sorry

/-- Reducedness, connectedness, and dimension one of the geometric fibres of a
family of curves are invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_geometricallyReducedConnectedDim1
    (S : Scheme.{u}) :
    (geometricallyReducedConnectedDim1 S).IsClosedUnderIsomorphisms := sorry

/-- For every family of curves, an open of its base represents reducedness,
connectedness, and dimension one of geometric fibres under every cartesian
morphism of families. -/
theorem exists_geometricallyReducedConnectedDim1_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      geometricallyReducedConnectedDim1 S Q ↔ Set.range (baseMap φ).left ⊆ U := sorry

/-- A proper scheme of dimension at most one over a field defines a family with
reduced, connected geometric fibres of dimension one if and only if it is
geometrically reduced, geometrically connected, and of dimension one. -/
theorem classifying_factorsThrough_geometricallyReducedConnectedDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    geometricallyReducedConnectedDim1 (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X ∧
        GeometricallyConnected X.hom ∧ topologicalKrullDim X.left = 1 := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
