/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator
import StacksCheckRecall

/-!
# Definition 18.34.1 compatibility entry point

The site-level differential-operator predicate and its sectionwise
computation rule are owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂) {F G : ringedSiteModuleCategory J O₂}
variable (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
variable (k : ℕ)

/- Definition 18.34.1: differential operators between module sheaves relative
to a morphism of commutative ring sheaves are defined objectwise on sections. -/
@[stacks 09CR] #check (IsDifferentialOperatorOfOrder φ D k : Prop)

variable (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ)

/- The sectionwise application API returns the canonical bundled-module predicate. -/
#check
  (IsDifferentialOperatorOfOrder.app φ D hD X :
    ModuleCat.IsDifferentialOperatorOfOrder (φ.hom.app X).hom (D.val.app X) k)

end SheafOfModules.RingedSite
