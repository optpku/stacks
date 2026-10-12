/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_27_3_Comparison
public import stacks_project.Chap66.Lemma_66_27_3_Space
import StacksCheckRecall

/-!
# Lemma 66.27.3

An étale sheaf of sets on an algebraic space determines, under a set-theoretic
smallness hypothesis, an algebraic space étale over the original space, recovering
the sheaf as the associated representable sheaf and as extension by zero of the
terminal sheaf.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.27.3 (1): the functor `X` associated to `F` is an algebraic space. -/
@[stacks 0GF6] #check sheafSpace

/- Lemma 66.27.3 (2): the map `X ⟶ Y` is an étale morphism of algebraic spaces. -/
@[stacks 0GF6] #check instEtale_sheafSpaceTo

/- Lemma 66.27.3 (3): via `Sh(Y_étale) = Sh(Y_spaces,étale)` we have `F ≅ h_X`. -/
@[stacks 0GF6] #check sheafSpace_yonedaIso

/- Lemma 66.27.3 (4): `F ≅ f_small,! *`, where `*` is the terminal object of
`Sh(X_étale)` and `f_small,! *` is the sheafification of the Sites formula
`V ↦ Σ_{φ : V ⟶ X over Y} PUnit`. -/
@[stacks 0GF6] #check sheafSpace_shriekIso
