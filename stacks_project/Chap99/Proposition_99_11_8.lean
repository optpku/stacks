/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap99.Lemma_99_11_7_Pushforward
public import stacks_project.Chap99.Proposition_99_8_4_Representable
public import stacks_project.Chap99.Situation_99_11_1

/-!
# Proposition 99.11.8

If `f : X ⟶ B` is a flat, finitely presented, proper morphism of algebraic
spaces over a scheme `S`, and `O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for
every scheme `T` over `B`, then the Picard functor `Pic_{X/B}` is an algebraic
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proposition 99.11.8: let `S` be a scheme and let `f : X ⟶ B` be a morphism
of algebraic spaces over `S`. If `f` is flat, of finite presentation, and
proper, and `O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for every scheme `T`
over `B`, then `picardFunctor f` (`Pic_{X/B}`) is an algebraic space. -/
@[stacks 0D2C]
theorem picardFunctor_isAlgebraicSpaceOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsAlgebraicSpaceOver (picardFunctor f).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
