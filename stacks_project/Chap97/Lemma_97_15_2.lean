module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap74.Lemma_74_11_29_Instances
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# First-order lifts of finite locally free LCI morphisms

An unramified local complete intersection morphism `Z ⟶ X` that is finite
locally free of degree `d` over an affine first-order thickening `U ⊂ U'`
lifts along a flat ambient algebraic space `X'` to a finite locally free
first-order thickening `Z'`.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

/-- Lemma 97.15.2: Let `U ⊂ U'` be a first-order thickening of affine algebraic
spaces. Let `X'` be an algebraic space flat over `U'`, and let `X` be cartesian
as `U ×_{U'} X'`. Let `Z ⟶ U` be finite locally free of degree `d`, and let
`f : Z ⟶ X` be unramified and a local complete intersection morphism. Then
there exist an algebraic space `Z'` and maps filling a commutative diagram
`(Z ⊂ Z') ⟶ (X ⊂ X')` over `(U ⊂ U')` such that `Z' ⟶ U'` is finite locally
free of degree `d` and `Z` is cartesian as `U ×_{U'} Z'`. -/
@[stacks 06D8]
theorem exists_finiteLocallyFreeOfRank_lift
    {S : Scheme.{u}} {U U' X X' Z : AlgebraicSpace S}
    (iU : U ⟶ U') (pX' : X' ⟶ U') (pX : X ⟶ U) (iX : X ⟶ X')
    (pZ : Z ⟶ U) (f : Z ⟶ X)
    [IsAffine U] [IsAffine U'] [IsFirstOrderThickening iU] [Flat pX']
    (hX : IsPullback pX iX iU pX') (d : ℕ) [FiniteLocallyFree pZ]
    [SheafOfModules.IsFiniteLocallyFreeOfRank d (Hom.pushforwardStructureModule pZ)]
    [Unramified f] [IsLocalCompleteIntersection f] (hZU : f ≫ pX = pZ) :
    ∃ (Z' : AlgebraicSpace S) (iZ : Z ⟶ Z') (pZ' : Z' ⟶ U') (f' : Z' ⟶ X'),
      IsFirstOrderThickening iZ ∧ CommSq f iZ iX f' ∧ f' ≫ pX' = pZ' ∧
        FiniteLocallyFree pZ' ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank d
              (Hom.pushforwardStructureModule pZ') ∧
            IsPullback pZ iZ iU pZ' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
