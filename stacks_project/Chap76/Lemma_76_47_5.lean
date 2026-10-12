/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap76.Definition_76_47_1_Perfect

/-!
# Derived pushforward of perfect complexes along perfect proper morphisms

Along a perfect proper morphism of algebraic spaces with Noetherian target,
derived pushforward preserves perfect objects of `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 76.47.5: let `S` be a scheme and let `Y` be a Noetherian algebraic space
over `S`. Let `f : X ⟶ Y` be a perfect proper morphism of algebraic spaces. If
`E` is a perfect object of `D(𝒪_X)`, then `(Modules.pushforwardDerived f).obj E`
is a perfect object of `D(𝒪_Y)`. -/
@[stacks 0E4U]
theorem pushforwardDerived_isPerfect_of_perfect_of_proper
    (f : X ⟶ Y) [Perfect f] [Proper f] [IsNoetherian Y]
    (E : ModuleDerived X) (hE : IsPerfect E) :
    IsPerfect ((Modules.pushforwardDerived f).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
