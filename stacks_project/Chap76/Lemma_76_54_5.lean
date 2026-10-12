/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap76.Lemma_76_36_10
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Relatively perfect complexes over a Jacobson pair

If `(R, I)` is a ring with `I` contained in the Jacobson radical and
`f : X ⟶ Spec R` is proper, flat, and of finite presentation, then a
pseudo-coherent object of `D(𝒪_X)` is `S`-perfect as soon as its derived
restriction to the special fibre is `S₀`-perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.54.5: Let `(R, I)` be a pair consisting of a ring and an ideal `I`
contained in the Jacobson radical. Set `S = Spec R` and `S₀ = Spec (R ⧸ I)`.
Let `X` be an algebraic space over `R` whose structure morphism
`f : X ⟶ S` is proper, flat, and of finite presentation. Denote `X₀` the fibre
product of `f` with `specQuotientι I` (the same fibre product as `S₀ ×_S X`).
Let `E` in `D(𝒪_X)` be pseudo-coherent. If the derived restriction `E₀` of `E`
to `X₀` is `S₀`-perfect, then `E` is `S`-perfect. -/
@[stacks 0DL5]
theorem isPerfectRelativeTo_of_quotient_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f] [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E)
    (hE₀ : IsPerfectRelativeTo (Limits.pullback.snd f (specQuotientι I))
      ((pullback (Limits.pullback.fst f (specQuotientι I))).obj E)) :
    IsPerfectRelativeTo f E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
