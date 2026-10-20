/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
variable
    [∀ G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction f).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/- Definition 59.66.1: for a finite étale morphism `f : Y ⟶ X` of schemes, the
natural map `f_* f⁻¹ ⟶ 𝟭` of abelian sheaves on the small étale site of `X`
(the counit of `f_! ⊣ f⁻¹`, using `f_* = f_!`) is called the trace. -/
@[stacks 03SE] #check
  (AlgebraicGeometry.Scheme.abelianEtaleTrace f :
    etaleRestrictionSheaf f AddCommGrpCat.{w} ⋙ abelianExtensionByZero f ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{w}))

end AlgebraicGeometry.Scheme
