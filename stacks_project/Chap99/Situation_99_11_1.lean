/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Situation_99_11_1_Functor
public import stacks_project.Chap99.Situation_99_11_1_PicardGroup
public import stacks_project.Chap99.Situation_99_11_1_Pullback

/-!
# The Picard functor of a morphism of algebraic spaces

Situation 99.11.1 introduces the fppf sheaf `Pic_{X/B}` associated to a
morphism of algebraic spaces, as the sheafification of `T ↦ Pic(X_T)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativePicard
open AlgebraicGeometry.AlgebraicSpace.PreRelation (schemesOverFppf)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Situation 99.11.1: let `S` be a scheme, and let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. The Picard functor `Pic_{X/B}` is the fppf
sheafification of the functor `(Sch/B)ᵒᵖ ⥤ Sets` sending a scheme `T` over `B`
to the group `Pic(X_T)`, where `X_T = X ×_B T`. -/
@[stacks 0D25]
abbrev picardFunctor (f : X ⟶ B) :=
  RelativePicard.functor f

/-- The underlying presheaf of `picardFunctor f` is the fppf sheafification of
`T ↦ Pic(X_T)`. -/
theorem picardFunctor_val (f : X ⟶ B) :
    (picardFunctor f).obj = (schemesOverFppf B).sheafify (RelativePicard.presheaf f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
