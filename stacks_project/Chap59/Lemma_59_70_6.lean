/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZeroComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/- Lemma 59.70.6 (1): for a separated étale morphism `j`, the abelian-sheaf
extension by zero admits a functorial comparison to the small étale direct
image whose components are monomorphisms. -/
@[stacks 0F4L] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZeroToDirectImage_app_mono j :
    ∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w},
      Mono ((abelianExtensionByZeroToDirectImage j).app F))

variable {Λ : Type w} [Ring Λ]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/- Lemma 59.70.6 (2): for a separated étale morphism `j`, the `Λ`-module-sheaf
extension by zero admits a functorial comparison to the small étale direct
image whose components are monomorphisms. -/
@[stacks 0F4L] #check
  (AlgebraicGeometry.Scheme.moduleExtensionByZeroToDirectImage_app_mono j :
    ∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ),
      Mono ((moduleExtensionByZeroToDirectImage j).app F))

end AlgebraicGeometry.Scheme
