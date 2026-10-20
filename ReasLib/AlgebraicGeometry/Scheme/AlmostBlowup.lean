module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup

/-!
# Almost blowup squares

This file defines when the canonical square determined by a scheme morphism and a closed center
is an almost blowup square.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The canonical square determined by a morphism `b : X' ⟶ X` and a closed center
`I.subschemeι : I.subscheme ⟶ X` is an almost blowup square when the center is finitely
presented, its inverse image in `X'` is locally principal, `b` is proper and finitely presented,
and the closed subscheme of `X'` cut out by sections supported on the inverse-image center is the
blowup of `X` in `I`. -/
def IsAlmostBlowupSquare {X X' : Scheme.{u}} (b : X' ⟶ X)
    (I : X.IdealSheafData) : Prop :=
  LocallyOfFinitePresentation I.subschemeι ∧
    IsLocallyPrincipalClosedSubscheme (I.comap b).subschemeι ∧
    IsProper b ∧ LocallyOfFinitePresentation b ∧
    IsBlowup (strictTransformFst b (I.comap b) (𝟙 X)) I

/-- The defining conditions of the canonical almost blowup square attached to `b` and `I`. -/
theorem isAlmostBlowupSquare_iff {X X' : Scheme.{u}} (b : X' ⟶ X)
    (I : X.IdealSheafData) :
    IsAlmostBlowupSquare b I ↔
      LocallyOfFinitePresentation I.subschemeι ∧
      IsLocallyPrincipalClosedSubscheme (I.comap b).subschemeι ∧
      IsProper b ∧ LocallyOfFinitePresentation b ∧
      IsBlowup (strictTransformFst b (I.comap b) (𝟙 X)) I := sorry

end AlgebraicGeometry
