/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap71.Lemma_71_12_3_ClosedImmersion
public import stacks_project.Chap71.Lemma_71_12_3_OnTarget

/-!
# Lemma 71.12.3

With the Lemma 71.12.1 setup, if 𝒜_d ⟶ ℬ_d is surjective for d ≫ 0, then
U(ψ) = Q, r_ψ : Q ⟶ P is a closed immersion, and each
θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) is surjective, but not an isomorphism in general
even if 𝒜 ⟶ ℬ is surjective.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.12.3 (1)
With hypotheses and notation as in Lemma 71.12.1, if 𝒜_d ⟶ ℬ_d is an
epimorphism for d ≫ 0, then U(ψ) = Q.
-/
@[stacks 085H] #check RelativeProjMap.domain_eq_id_of_eventually_surjective

/- Lemma 71.12.3 (2)
The induced morphism r_ψ : Q ⟶ P is a closed immersion.
-/
@[stacks 085H] #check RelativeProjMap.mapOnTarget_isClosedImmersion_of_eventually_surjective

/- Lemma 71.12.3 (3)
The maps θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) are surjective, but not isomorphisms in
general (even if 𝒜 ⟶ ℬ is surjective).
-/
@[stacks 085H] #check RelativeProjMap.thetaOnTarget_epi_of_eventually_surjective
