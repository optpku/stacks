module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.VersalAt
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
import Mathlib.Tactic.CrossRefAttribute

/-! # Openness of smoothness for adic morphisms of formal algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidsOver
open FiberedCategoryOver Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- An adic morphism from the completion of a scheme locally of finite type
over a locally Noetherian base to a locally Noetherian formal algebraic space
with locally finite-type reduction is smooth on one open neighbourhood of a
closed point where it is versal. Smoothness means representability by algebraic
spaces with smooth Yoneda pullbacks. -/
@[stacks 0GI9]
theorem exists_isSmooth_nhd {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    {W : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian W] (R : ReductionData W)
    [AlgebraicSpace.LocallyOfFiniteType (AlgebraicSpace.SchemeRealization.toBase R.space)]
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W)
    (hg : representableByAlgebraicSpaces g) (v : V.left) (hv : IsClosed {v})
    [IsFiniteTypePoint v] [IsVersalAt Z g v] :
    ∃ V' : V.left.Opens,
      v ∈ V' ∧
        representableByAlgebraicSpaces (restrictAlong Z V' ≫ g) ∧
          ∀ (ha : representableByAlgebraicSpaces (restrictAlong Z V' ≫ g))
            ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ W),
            AlgebraicSpace.Smooth (ha.pullbackHom ξ) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
