/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap84.Lemma_84_5_4_Comparison
import StacksCheckRecall

/-!
# Lemma 84.5.4

Derived cohomology on `(Spaces/X)_étale` agrees with small-site cohomology after
`π_X⁻¹`, `Lπ_X^*`, `f_small⁻¹`, `Lf_small^*`, `i_f⁻¹`, and `i_f^*`.
The structure sheaf `𝒪` on `(Spaces/X)_étale` is `U ↦ Γ(U, 𝒪_U)`, not `π_X⁻¹ 𝒪_X`.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Etale.Derived

noncomputable section

universe u

/- Lemma 84.5.4 (1): ordinary derived cohomology on the big étale site over `X` agrees with
the cohomology of the identity inverse image on the small étale site. -/
@[stacks 0DGB] #check etaleCohomology_piInverseImage

/- Lemma 84.5.4 (2): module-valued derived cohomology on the big étale site agrees with the
cohomology of the identity pullback on the small étale site. -/
@[stacks 0DGB] #check etaleModuleCohomology_piPullback

/- Lemma 84.5.4 (3): ordinary derived cohomology on `Y` agrees with small-site cohomology after
the inverse image associated to `f : Y ⟶ X`. -/
@[stacks 0DGB] #check etaleCohomology_smallInverseImage

/- Lemma 84.5.4 (4): module-valued derived cohomology on `Y` agrees with small-site cohomology
after the derived pullback associated to `f : Y ⟶ X`. -/
@[stacks 0DGB] #check etaleModuleCohomology_smallPullback

/- Lemma 84.5.4 (5): ordinary derived cohomology on the big site over `X` agrees with cohomology
on the small étale site of `Y` after relocalization. -/
@[stacks 0DGB] #check etaleCohomology_relocalization

/- Lemma 84.5.4 (6): module-valued derived cohomology on the big site over `X` agrees with
cohomology on the small étale site of `Y` after relocalization. -/
@[stacks 0DGB] #check etaleModuleCohomology_relocalization
