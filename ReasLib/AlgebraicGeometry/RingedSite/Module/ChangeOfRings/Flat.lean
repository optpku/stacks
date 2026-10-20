/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat modules and same-site extension of scalars

Extension of scalars is the canonical owner of same-site base change for module sheaves.  This
leaf records that it preserves flat objects and retains a pullback-form compatibility theorem for
older code expressed through the ringed-site pullback functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ O₁ : Sheaf J CommRingCat.{u}}

namespace IsFlat

/-- Lemma 18.28.13 (05V4): same-site extension of scalars preserves flat module sheaves. -/
@[stacks 05V4]
instance extendAlong (alpha : O₀ ⟶ O₁)
    (M : ringedSiteModuleCategory J O₀) [IsFlat O₀ M] :
    IsFlat O₁ ((SheafOfModules.RingedSite.extendAlong alpha).obj M) := sorry

/-- The pullback presentation of same-site extension of scalars preserves flat module sheaves. -/
theorem pullbackSameSite (alpha : O₀ ⟶ O₁)
    (M : ringedSiteModuleCategory J O₀) [IsFlat O₀ M] :
    IsFlat O₁ ((SheafOfModules.pullback (ringedSiteStructureMap alpha)).obj M) := sorry

end IsFlat

end SheafOfModules.RingedSite
