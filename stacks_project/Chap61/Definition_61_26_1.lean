/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

section SetValued

variable (j : U ⟶ X) [WeaklyEtale j]
variable [∀ F : U.ProEtᵒᵖ ⥤ Type w,
  (ProEt.restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology X) (Type w)]

/- Definition 61.26.1 (1): extension by zero for sheaves of sets along a
weakly étale morphism is left adjoint to pro-étale restriction, as a functor
Sh(U_proétale) ⥤ Sh(X_proétale). -/
@[stacks 09AE] #check
  (AlgebraicGeometry.Scheme.ProEt.sheafExtensionByZero_adjunction j :
    AlgebraicGeometry.Scheme.ProEt.sheafExtensionByZero j ⊣
      AlgebraicGeometry.Scheme.ProEt.restrictionSheaf j (Type w))

end SetValued

section AbelianGroups

variable (j : U ⟶ X) [WeaklyEtale j]
variable [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
  (ProEt.restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}]

/- Definition 61.26.1 (2): extension by zero for sheaves of abelian groups
along a weakly étale morphism is left adjoint to pro-étale restriction. -/
@[stacks 09AE] #check
  (AlgebraicGeometry.Scheme.ProEt.abelianExtensionByZero_adjunction j :
    AlgebraicGeometry.Scheme.ProEt.abelianExtensionByZero j ⊣
      AlgebraicGeometry.Scheme.ProEt.restrictionSheaf j AddCommGrpCat.{w})

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable (j : U ⟶ X) [WeaklyEtale j]
variable [∀ F : U.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ,
  (ProEt.restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]

/- Definition 61.26.1 (3): extension by zero for sheaves of `Λ`-modules along a
weakly étale morphism is left adjoint to pro-étale restriction. -/
@[stacks 09AE] #check
  (AlgebraicGeometry.Scheme.ProEt.moduleExtensionByZero_adjunction j :
    AlgebraicGeometry.Scheme.ProEt.moduleExtensionByZero j ⊣
      AlgebraicGeometry.Scheme.ProEt.restrictionSheaf j (ModuleCat.{w} Λ))

end Modules

end AlgebraicGeometry.Scheme
