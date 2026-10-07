module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_11_1_Sequence

/-!
# Lemma 67.11.1

Pushforward of an `𝒪_X`-module along a morphism of algebraic spaces is computed
from a surjective étale scheme atlas by the exact sequence whose second arrow
is the difference of the two kernel-pair restrictions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U : Over S}

/-- Lemma 67.11.1: let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces
over `S`. Let `π : U ⟶ X` be a surjective étale morphism from a scheme. Set
`R = U ×_X U` with projections `t, s : R ⟶ U`, and write `a = π ≫ f` and
`b = t ≫ a` for the induced morphisms. For any `F` in `X.Modules` the sequence
`0 ⟶ f_* F ⟶ a_*(F|_U) ⟶ b_*(F|_R)` is exact, where the second arrow is the
difference `t* - s*`. -/
@[stacks 03M8]
theorem pushforward_exact (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π)
    [Etale π] [Surjective π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).Exact ∧ Mono (pushforwardIncl f π F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
