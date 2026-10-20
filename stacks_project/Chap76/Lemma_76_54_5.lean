/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.Jacobson

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 76.54.5: Let `(R, I)` be a pair consisting of a ring and an ideal `I`
contained in the Jacobson radical. Set `S = Spec R` and `S₀ = Spec (R ⧸ I)`.
Let `X` be an algebraic space over `R` whose structure morphism
`f : X ⟶ S` is proper, flat, and of finite presentation. Denote `X₀` the fibre
product of `f` with `specQuotientι I` (the same fibre product as `S₀ ×_S X`).
Let `E` in `D(𝒪_X)` be pseudo-coherent. If the derived restriction `E₀` of `E`
to `X₀` is `S₀`-perfect, then `E` is `S`-perfect. -/
@[stacks 0DL5] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPerfectRelativeTo_of_quotient_of_le_jacobson :
    ∀ {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f] [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E)
    (hE₀ : IsPerfectRelativeTo (Limits.pullback.snd f (specQuotientι I))
      ((pullback (Limits.pullback.fst f (specQuotientι I))).obj E)),
    IsPerfectRelativeTo f E)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
