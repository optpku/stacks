/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Flat
public import ReasLib.CategoryTheory.Monoidal.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertibility of determinant sheaves

The annihilator determinant of a module sheaf which is locally a retract of a finite free
module sheaf is tensor-invertible.  The flat finitely presented form is a direct consequence of
the reusable finite-free-retract criterion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The annihilator determinant of a module sheaf which is locally a retract of finite free
module sheaves is tensor-invertible. -/
@[stacks 0FJN "local finite-free-retract form", instance]
theorem isInvertible_of_isLocal
    (F : ringedSiteModuleCategory J 𝒪) [FiniteFreeRetract.IsLocal F] :
    isInvertibleObject (sheaf F) := sorry

/-- The annihilator determinant of a flat finitely presented module sheaf is
tensor-invertible. -/
@[stacks 0FJN "ringed-site form", instance]
theorem isInvertible
    (F : ringedSiteModuleCategory J 𝒪) [F.IsFinitePresentation] [IsFlat 𝒪 F] :
    isInvertibleObject (sheaf F) := sorry

end SheafOfModules.RingedSite.Determinant
