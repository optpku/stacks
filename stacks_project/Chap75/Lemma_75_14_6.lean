module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes.ElementaryDistinguishedSquare
import StacksCheckRecall

/-!
# Approximation along an elementary distinguished square

If `(U ⊂ X, f : V ⟶ X)` is an elementary distinguished square of algebraic
spaces with `U` quasi-compact, `V` affine, and `U ×_X V` quasi-compact, then
approximation by perfect complexes on `U` implies the same on `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 75.14.6. Approximation by perfect complexes descends along an
elementary distinguished square with quasi-compact open member, affine étale
member, and quasi-compact overlap. -/
@[stacks 08HN] #check
  (AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes.of_isElementaryDistinguishedSquare :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X),
      [IsElementaryDistinguishedSquare j f] → [IsQuasiCompact U] → [IsAffine V] →
      [IsQuasiCompact (pullback j f)] →
      HasApproximationByPerfectComplexes U → HasApproximationByPerfectComplexes X)
