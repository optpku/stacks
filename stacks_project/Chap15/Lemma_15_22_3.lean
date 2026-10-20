/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
import StacksCheckRecall

/-!
Lemma 15.22.3 (0AUR): localization of a torsion-free module over a domain is torsion-free over
the localized domain.

@stack 0AUR
-/

@[expose] public section

open Module

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M] [IsTorsionFree R M]

/- Lemma 15.22.3 (0AUR): `LocalizedModule S M` is torsion-free over `Localization S`. -/
@[stacks 0AUR]
#check
  (IsLocalizedModule.isTorsionFree (LocalizedModule.mkLinearMap S M) S :
    IsTorsionFree (Localization S) (LocalizedModule S M))
