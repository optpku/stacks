module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.AnalyticallyUnramified
import StacksCheckRecall

/-!
# Finiteness of absolute normalization over an analytically unramified local ring
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 89.6.3: Let `(A, 𝔪)` be a local Noetherian ring. Let `X` be an algebraic
space over `A`. Assume `A` is analytically unramified, `X` is locally of finite
type over `A`, and `X ⟶ Spec(A)` is étale at every point of codimension `0` in
`X`. Then the normalization of `X` is finite over `X`. -/
@[stacks 0BHR] #check
  (AlgebraicGeometry.AlgebraicSpace.isFinite_normalizationTo_of_analyticallyUnramified_of_codimZeroEtale :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAnalyticallyUnramified A] (X : AlgebraicSpace (Spec (.of A)))
    [LocallyOfFiniteType (SchemeRealization.toBase X)],
    (∀ x : Points X, x ∈ codimZeroPoints X → EtaleAt (SchemeRealization.toBase X) x) →
    IsFinite X.normalizationTo)

end AlgebraicGeometry.AlgebraicSpace
