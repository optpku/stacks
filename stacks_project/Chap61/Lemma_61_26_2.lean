/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleExtensionByZero
import StacksCheckRecall

/-!
# Lemma 61.26.2

Étale extension by zero commutes with inverse image along the
étale-to-pro-étale comparison of small sites.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
  (ProEt.restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleToProEt U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology U) AddCommGrpCat.{w}]
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (etaleToProEt X).op.HasLeftKanExtension F]

variable (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{w})

/- Lemma 61.26.2: for an étale morphism `j : U ⟶ X`, inverse image along the
étale-to-pro-étale comparison commutes with abelian extension by zero. -/
@[stacks 09AF] #check (AlgebraicGeometry.Scheme.abelianExtensionByZero_etaleProetale j G :
  IsIsomorphic
    ((etaleToProEtPullback X AddCommGrpCat.{w}).obj
      ((abelianExtensionByZero j).obj G))
    ((ProEt.abelianExtensionByZero j).obj
      ((etaleToProEtPullback U AddCommGrpCat.{w}).obj G)))

end

end AlgebraicGeometry.Scheme
