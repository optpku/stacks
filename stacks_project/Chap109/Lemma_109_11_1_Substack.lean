module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap75.Lemma_75_26_8_GeometricFibres
public import stacks_project.Chap109.Lemma_109_10_1_Substack

/-!
# The object property of geometrically reduced connected curves of dimension 1

`𝒞urves^{grc, 1}` is the full subcategory of families of curves whose
geometric fibres are reduced, connected, and of dimension `1`. Membership is
the source-facing packaging of a classifying morphism factoring through that
open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves with reduced, connected geometric
fibres of dimension `1`, corresponding to the open substack `𝒞urves^{grc, 1}`. -/
def geometricallyReducedConnectedDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    Hom.HasReducedGeometricFibres (hom P) ∧
      Hom.HasConnectedGeometricFibres (hom P) ∧
        ∀ ybar : GeometricPoint (ofOver (base P)),
          dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1

/-- Membership in `geometricallyReducedConnectedDim1` means the geometric fibres
of the structure morphism are reduced, connected, and of dimension `1`. -/
theorem geometricallyReducedConnectedDim1_iff {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1 S P ↔
      Hom.HasReducedGeometricFibres (hom P) ∧
        Hom.HasConnectedGeometricFibres (hom P) ∧
          ∀ ybar : GeometricPoint (ofOver (base P)),
            dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1 :=
  sorry

/-- The geometrically reduced, connected, dimension-`1` property of families of
curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_geometricallyReducedConnectedDim1
    (S : Scheme.{u}) :
    (geometricallyReducedConnectedDim1 S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
