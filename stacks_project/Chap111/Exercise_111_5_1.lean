/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Module
import StacksCheckRecall

@[expose] public section

universe u v

open scoped TensorProduct

variable {A : Type u} [CommRing A] (S : Submonoid A) {M : Type v} [AddCommGroup M]
  [Module A M]

/- Exercise 111.5.1 (1): for an `A`-module `M`, the localized module `S⁻¹M` is
canonically identified with `S⁻¹A ⊗[A] M` as an `S⁻¹A`-module. -/
@[stacks 02CQ]
#check (Localization.moduleEquivTensorProduct S M :
  LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[A] M)

/- Exercise 111.5.1 (2): `S⁻¹A` is flat over `A`. -/
@[stacks 02CQ]
#check (Localization.flatModule S : Module.Flat A (Localization S))
