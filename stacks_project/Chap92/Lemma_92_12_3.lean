/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Tor
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

/- Lemma 92.12.3: For the polynomial ring `P = MvPolynomial σ A` and its variable ideal
`I = MvPolynomial.idealOfVars σ A`, the inclusions `I ^ (n + 1) ≤ I ^ n` induce zero maps
on `Tor_i^P(A, -)` for every `i` and `n`, with `A` acted on through `constantCoeff`. -/
@[stacks 08RE] #check (MvPolynomial.tor_map_pow_idealOfVars_eq_zero :
  ∀ {A : Type u} [CommRing A] {σ : Type u} (i n : ℕ),
    ((CategoryTheory.Tor (ModuleCat (MvPolynomial σ A)) i).obj
      ((ModuleCat.restrictScalars (MvPolynomial.constantCoeff : MvPolynomial σ A →+* A)).obj
        (ModuleCat.of A A))).map
      (ModuleCat.ofHom (Submodule.inclusion
        (Ideal.pow_le_pow_right (I := MvPolynomial.idealOfVars σ A) n.le_succ))) = 0)
