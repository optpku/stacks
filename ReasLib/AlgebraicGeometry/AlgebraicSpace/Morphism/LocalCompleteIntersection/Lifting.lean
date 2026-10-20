module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# First-order lifts of finite locally free LCI morphisms

An unramified local complete intersection morphism into the closed fiber of a
flat algebraic space over an affine first-order thickening admits a lift whose
source remains finite locally free of the same degree over the thickened base.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

/-- Let `U ⊂ U'` be a first-order thickening of affine algebraic spaces, and let
`X` be the pullback to `U` of an algebraic space `X'` flat over `U'`. An
unramified local complete intersection morphism `f : Z ⟶ X` over `U`, with
`Z ⟶ U` finite locally free of degree `d`, lifts to a morphism `Z' ⟶ X'`
over `U'`, where `Z' ⟶ U'` is finite locally free of degree `d` and its
pullback to `U` is the first-order closed fiber `Z`. -/
theorem exists_finiteLocallyFreeOfRank_lift
    {S : Scheme.{u}} {U U' X X' Z : AlgebraicSpace S}
    (iU : U ⟶ U') (pX' : X' ⟶ U') (pX : X ⟶ U) (iX : X ⟶ X')
    (pZ : Z ⟶ U) (f : Z ⟶ X)
    [IsAffine U] [IsAffine U'] [IsFirstOrderThickening iU] [Flat pX']
    (hX : IsPullback pX iX iU pX') (d : ℕ) [FiniteLocallyFreeOfRank pZ d]
    [Unramified f] [IsLocalCompleteIntersection f] (hZU : f ≫ pX = pZ) :
    ∃ (Z' : AlgebraicSpace S) (iZ : Z ⟶ Z') (pZ' : Z' ⟶ U') (f' : Z' ⟶ X'),
      IsFirstOrderThickening iZ ∧ CommSq f iZ iX f' ∧ f' ≫ pX' = pZ' ∧
        FiniteLocallyFreeOfRank pZ' d ∧ IsPullback pZ iZ iU pZ' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
