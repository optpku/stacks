/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_33_1_Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 66.33.1: Let X be an algebraic space over Spec ℤ. Let T be an affine scheme.
The map Mor(X, T) ⟶ Hom(Γ(T, ⊤), Γ(X, 𝒪_X)) which maps f to f^♯ on global sections
is bijective. -/
@[stacks 05Z1] #check AlgebraicGeometry.AlgebraicSpace.GlobalSections.homEquivAffine
#check AlgebraicGeometry.AlgebraicSpace.GlobalSections.homEquivAffine_apply
#check AlgebraicGeometry.AlgebraicSpace.GlobalSections.homEquivAffine_symm_apply
