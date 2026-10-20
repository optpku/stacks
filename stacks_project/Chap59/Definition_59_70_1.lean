/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

section SetValued

variable (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ Type w,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology (Type w)]

/- Definition 59.70.1 (1): extension by zero for sheaves of sets is left
adjoint to étale restriction. -/
@[stacks 03S3] #check
  (AlgebraicGeometry.Scheme.sheafExtensionByZero_adjunction j :
    sheafExtensionByZero j ⊣ etaleRestrictionSheaf j (Type w))

end SetValued

section AbelianGroups

variable (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/- Definition 59.70.1 (2): extension by zero for sheaves of abelian groups
is left adjoint to étale restriction. -/
@[stacks 03S3] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_adjunction j :
    abelianExtensionByZero j ⊣ etaleRestrictionSheaf j AddCommGrpCat.{w})

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/- Definition 59.70.1 (3): extension by zero for sheaves of `Λ`-modules is
left adjoint to étale restriction. -/
@[stacks 03S3] #check
  (AlgebraicGeometry.Scheme.moduleExtensionByZero_adjunction j :
    moduleExtensionByZero j ⊣ etaleRestrictionSheaf j (ModuleCat.{w} Λ))

end Modules

end AlgebraicGeometry.Scheme
