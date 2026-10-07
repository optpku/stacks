module

import StacksCheckRecall
public import stacks_project.Chap71.Lemma_71_12_4_Isomorphism

/-!
# Lemma 71.12.4

With the hypotheses and notation of Lemma 71.12.1, if the nonnegative graded pieces of
ψ are isomorphisms in all sufficiently large degrees, then U(ψ) equals Q, the induced
map r_ψ : Q ⟶ P is an isomorphism, and each twist comparison
θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.12.4 (1)
Eventual isomorphy of 𝒜_d → ℬ_d for d ≫ 0 makes the natural domain equal to Q.
-/
@[stacks 085I] #check RelativeProjMap.domain_eq_id_of_eventually_isIso

/- Lemma 71.12.4 (2)
The full-source morphism r_ψ : Q ⟶ P is then an isomorphism.
-/
@[stacks 085I] #check RelativeProjMap.mapOnTarget_isIso_of_eventually_isIso

/- Lemma 71.12.4 (3)
Each full-source integral-twist comparison θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) is an isomorphism.
-/
@[stacks 085I] #check RelativeProjMap.thetaOnTarget_isIso_of_eventually_isIso
