/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Fiber.FieldExtension
import StacksCheckRecall

@[expose] public section

/-! @stack 045N -/

universe u v w

open Algebra.TensorProduct
open scoped TensorProduct

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {S : Type w} [CommRing S] [Algebra k S] [IsNoetherianRing S]

/- Lemma 10.167.2 (Stacks tag `045N`): the essentially finite type
localization criterion is owned by the shared Cohen--Macaulay fiber API. -/
@[stacks 045N]
#check @Module.CohenMacaulay.FieldExtension.EssFiniteType.localizationAtPrime_iff_of_liesOver

end
