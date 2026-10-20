module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.RingTheory.AdicCompletion.AlgebraMap
public import stacks_project.Chap88.Lemma_88_30_1_BaseChange

/-!
# Base change equivalence for affine 88.30.0.1 categories

If `A → B` induces an isomorphism of `I`-adic completions, base change along
`Spec(B) → Spec(A)` is an equivalence of the 88.30.0.1 source categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- Lemma 88.30.1: Let `A → B` be a homomorphism of Noetherian rings inducing an
isomorphism of `I`-adic completions for some ideal `I ⊆ A` (for example if `B`
is the `I`-adic completion of `A`). Then base change along `algebraMapOver B hA`
is an equivalence from the category 88.30.0.1 for `(A, I)`, namely
`Source (specOver hA) (zeroLocusPoints hA I)`, to the category 88.30.0.1 for
`(B, I.map (algebraMap A B))`. -/
@[stacks 0AE5]
theorem isEquivalence_sourceBaseChangeAlgebraMap {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B)) :
    (sourceBaseChangeAlgebraMap B hA I).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong

namespace AdicCompletion

/-- If `B` is the `I`-adic completion of a Noetherian ring `A`, then the
canonical `extensionMap I` is bijective. -/
theorem bijective_extensionMap_adicCompletion {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    Function.Bijective
      (extensionMap I :
        AdicCompletion I A →+*
          AdicCompletion (I.map (algebraMap A (AdicCompletion I A)))
            (AdicCompletion I A)) :=
  sorry

end AdicCompletion
