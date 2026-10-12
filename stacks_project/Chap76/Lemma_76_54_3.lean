/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder

/-!
# Pseudo-coherence along finite-order thickenings of algebraic spaces

If `i : X ⟶ X'` is a finite-order thickening of algebraic spaces over a scheme
and `K'` is an object of `D(𝒪_{X'})` whose derived pullback `Li^* K'` is
pseudo-coherent, then `K'` itself is pseudo-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

/-- Lemma 76.54.3: Let `S` be a scheme. Let `i : X ⟶ X'` be a finite-order
thickening of algebraic spaces. Let `K'` in `D(𝒪_{X'})` be an object such that
`K = Li^* K'` is pseudo-coherent, where `Li^*` is `modulePullbackDerived i`.
Then `K'` is pseudo-coherent. -/
@[stacks 0DL3]
theorem isPseudoCoherent_of_pullback {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFiniteOrderThickening i] (K' : ModuleDerived X')
    (hK : IsPseudoCoherent X ((modulePullbackDerived i).obj K')) :
    IsPseudoCoherent X' K' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
