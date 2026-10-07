module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on a proper curve over a field is ample exactly when its degree is
positive. -/
theorem isAmple_iff_curveDegreeOfInvertible_pos
    {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    (ℒ : X.left.Modules) [Invertible ℒ] :
    IsAmple ℒ ↔
      0 < curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ := sorry

/-- An invertible module on a proper scheme of dimension at most one over a field is ample
exactly when its degree on every one-dimensional reduced irreducible component is positive. -/
theorem isAmple_iff_curveDegree_pos_on_oneDimensional_irreducibleComponents
    {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (ℒ : X.left.Modules) [Invertible ℒ]
    (hXdim : topologicalKrullDim X.left ≤ 1) :
    IsAmple ℒ ↔
      ∀ Z : irreducibleComponents X.left,
        ∀ hZdim : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1,
          0 < curveDegreeOfInvertible
            (X.left.irreducibleComponentSubschemeι Z ≫ X.hom) hZdim.le
            ((Scheme.Modules.pullback (X.left.irreducibleComponentSubschemeι Z)).obj ℒ) := sorry

end AlgebraicGeometry.Scheme.Modules
