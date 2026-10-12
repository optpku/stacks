/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Lemma_86_2_1_EtaleDualizing

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 86.2.1: let `S` be a scheme. Let `X` be a locally Noetherian algebraic space
over `S`. Let `K` be an object of `D_QCoh(𝒪_X)`. The following are equivalent: for every
étale morphism `U ⟶ X` where `U` is a scheme, the restriction `K|_U` is a dualizing
complex for `U`; and there exists a surjective étale morphism `U ⟶ X` where `U` is a
scheme such that `K|_U` is a dualizing complex for `U`. -/
@[stacks 0E4Y]
theorem isDualizingOnScheme_forall_iff_exists {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    forallEtaleScheme K ↔ existsSurjectiveEtaleScheme K :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
