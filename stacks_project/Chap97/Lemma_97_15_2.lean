module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Lifting
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme AlgebraicSpace)
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 97.15.2: Let `U ⊂ U'` be a first-order thickening of affine algebraic
spaces. Let `X'` be an algebraic space flat over `U'`, and let `X` be cartesian
as `U ×_{U'} X'`. Let `Z ⟶ U` be finite locally free of degree `d`, and let
`f : Z ⟶ X` be unramified and a local complete intersection morphism. Then
there exist an algebraic space `Z'` and maps filling a commutative diagram
`(Z ⊂ Z') ⟶ (X ⊂ X')` over `(U ⊂ U')` such that `Z' ⟶ U'` is finite locally
free of degree `d` and `Z` is cartesian as `U ×_{U'} Z'`. -/
@[stacks 06D8]
#check (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.exists_finiteLocallyFreeOfRank_lift :
    ∀ {S : Scheme.{u}} {U U' X X' Z : AlgebraicSpace S}
    (iU : U ⟶ U') (pX' : X' ⟶ U') (pX : X ⟶ U) (iX : X ⟶ X')
    (pZ : Z ⟶ U) (f : Z ⟶ X)
    [IsAffine U] [IsAffine U'] [IsFirstOrderThickening iU] [Flat pX']
    (hX : IsPullback pX iX iU pX') (d : ℕ) [FiniteLocallyFreeOfRank pZ d]
    [Unramified f] [IsLocalCompleteIntersection f] (hZU : f ≫ pX = pZ),
    ∃ (Z' : AlgebraicSpace S) (iZ : Z ⟶ Z') (pZ' : Z' ⟶ U') (f' : Z' ⟶ X'),
      IsFirstOrderThickening iZ ∧ CommSq f iZ iX f' ∧ f' ≫ pX' = pZ' ∧
        FiniteLocallyFreeOfRank pZ' d ∧ IsPullback pZ iZ iU pZ')
