/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w u₁ v₁

namespace AlgebraicGeometry.Scheme.ProEt

variable {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]

section Coefficients

variable (A : Type u₁) [Category.{v₁} A]

#check (restrictionSheaf j A : Sheaf (topology X) A ⥤ Sheaf (topology U) A)

variable [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (topology X) A]

#check (restrictionSheaf_isRightAdjoint j A : (restrictionSheaf j A).IsRightAdjoint)
#check (extensionByZero j A : Sheaf (topology U) A ⥤ Sheaf (topology X) A)
#check (extensionByZero_adjunction j A : extensionByZero j A ⊣ restrictionSheaf j A)

end Coefficients

section SetValued

variable [∀ F : U.ProEtᵒᵖ ⥤ Type w, (restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (topology X) (Type w)]

#check (sheafExtensionByZero j :
  Sheaf (topology U) (Type w) ⥤ Sheaf (topology X) (Type w))
#check (sheafExtensionByZero_adjunction j :
  sheafExtensionByZero j ⊣ restrictionSheaf j (Type w))

end SetValued

section AbelianGroups

variable [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w}, (restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{w}]

#check (abelianExtensionByZero j :
  Sheaf (topology U) AddCommGrpCat.{w} ⥤ Sheaf (topology X) AddCommGrpCat.{w})
#check (abelianExtensionByZero_adjunction j :
  abelianExtensionByZero j ⊣ restrictionSheaf j AddCommGrpCat.{w})

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable [∀ F : U.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]

#check (moduleExtensionByZero j :
  Sheaf (topology U) (ModuleCat.{w} Λ) ⥤ Sheaf (topology X) (ModuleCat.{w} Λ))
#check (moduleExtensionByZero_adjunction j :
  moduleExtensionByZero j ⊣ restrictionSheaf j (ModuleCat.{w} Λ))

end Modules

end AlgebraicGeometry.Scheme.ProEt
