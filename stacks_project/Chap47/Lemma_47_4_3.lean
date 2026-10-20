/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.ProjectiveCover
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.4.3: Every finite module over a local ring admits an essential surjection
from a finite free, hence projective, module. -/
@[stacks 08Y0] #check
  (Module.Finite.exists_fin_projectiveCover :
    ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
        [IsLocalRing R] [Module.Finite R M],
      ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M),
        f.range = ⊤ ∧ ∀ N : Submodule R (Fin n → R), N.map f = ⊤ → N = ⊤)
