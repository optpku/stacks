/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.Finite
public import ReasLib.Algebra.Module.Torsion.Stability

@[expose] public section

/-!
# Torsion stabilization after localization

This file isolates the reusable module-theoretic content of Ogoma's lemma.
The natural finiteness assumption is that the module itself is Noetherian;
Noetherian rings and finite modules are a common specialization.
-/

universe u v

namespace Module.IsTorsionStable

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [IsNoetherian A M]

/-- Lemma 16.10.1 (Ogoma) (Tag 07FC): if localization makes the torsion
submodules for `π` and `π ^ 2` equal, one denominator makes the corresponding
equality hold globally after every positive power of that denominator. -/
@[stacks 07FC]
theorem exists_denominator (S : Submonoid A) (π : A)
    (hlocal : IsTorsionStable (Localization S) (LocalizedModule S M)
      (algebraMap A (Localization S) π)) :
    ∃ s : S, ∀ n : ℕ+,
      IsTorsionStable A M (((s : A) ^ (n : ℕ)) * π) := sorry

end Module.IsTorsionStable
