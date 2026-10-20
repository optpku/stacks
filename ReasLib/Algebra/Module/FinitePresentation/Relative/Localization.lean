/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import ReasLib.Algebra.Module.FinitePresentation.Relative.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of relatively finitely presented modules

Relative finite presentation over a localized base descends after localizing the module once
more over the target algebra.

@stack 065A
-/

@[expose] public section

universe u v w

namespace Module

variable {R : Type u} [CommRing R] {f : R}
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable [Algebra.FiniteType (Localization.Away f) A]
variable {g : A} {M : Type w} [AddCommGroup M] [Module A M]

/-- Lemma 15.81.4 (065A): if `M` is finitely presented relative to the localized base
`Localization.Away f`, then its localization away from `g` is finitely presented relative to
`R`. -/
@[stacks 065A "relative finite presentation after localization"]
theorem finitePresentationRelativeTo_localizationAway_from_localizedBase
    (hM : FinitePresentationRelativeTo (Localization.Away f) A M) :
    FinitePresentationRelativeTo R (Localization.Away g) (LocalizedModule.Away g M) := sorry
/- Proof strategy: apply `FinitePresentationRelativeTo.baseChange` along
`A → Localization.Away g`, identify the tensor-product module with
`LocalizedModule.Away g M`, and then use `FinitePresentationRelativeTo.trans`; the principal
localization `R → Localization.Away f` is a finitely presented algebra. -/

end Module
