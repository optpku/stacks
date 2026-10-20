/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion.Primary

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Sheaf

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Coverwise annihilation by a power of `ℓ` is the defining condition. -/
theorem isLocallyPPowerTorsion_iff (ℓ : ℕ) (F : Sheaf J AddCommGrpCat.{w}) :
    IsLocallyPPowerTorsion ℓ F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          ∃ k : ℕ, (ℓ ^ k) • (F.obj.map I.f.op s) = 0 := sorry

namespace IsLocallyPPowerTorsion

/-- Sectionwise annihilation by a power of `ℓ` implies local `ℓ`-power torsion. -/
theorem ofSectionwise {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : ∀ (U : C) (s : F.obj.obj (op U)), ∃ k : ℕ, (ℓ ^ k) • s = 0) :
    IsLocallyPPowerTorsion ℓ F := sorry

/-- Local `ℓ`-power torsion implies local finite-order torsion when `ℓ` is positive. -/
theorem toIsLocallyTorsion {ℓ : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hℓ : 0 < ℓ) (hF : IsLocallyPPowerTorsion ℓ F) :
    IsLocallyTorsion F := sorry

end IsLocallyPPowerTorsion

end CategoryTheory.Sheaf

end
