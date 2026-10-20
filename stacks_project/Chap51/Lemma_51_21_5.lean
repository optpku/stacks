/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.IdealPower
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ModuleTor

universe u

/- Lemma 51.21.5: if `t` bounds the number of generators of an ideal `I` in a
Noetherian ring `A`, then one power of `I` annihilates
`Tor⁽i⁾[A](M, (A ⧸ (I ^ q)))` for every `A`-module `M`, every `i > t`, and every `q`. -/
@[stacks 0GA1]
#check (CategoryTheory.ModuleCat.Tor.exists_pow_le_annihilator_tor_quotient :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (t : ℕ)
    (h_generators : ∃ a : Fin t → I,
      I = Ideal.span (Set.range fun j ↦ (a j : A))),
    ∃ c : ℕ, ∀ (M : ModuleCat.{u} A) (i q : ℕ), t < i →
      I ^ c ≤ Module.annihilator A Tor⁽i⁾[A](M, (A ⧸ (I ^ q))))
