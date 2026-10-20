/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u v w

section SetValued

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type v)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type v,
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Definition 59.36.1 (1): the inverse-image functor on set-valued small étale
sheaves is left adjoint to the corresponding direct-image functor. -/
@[stacks 03Q0] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_sheafAdjunction f (Type v) :
      (Scheme.smallEtalePullback f).sheafPullback
        (Type v) Y.smallEtaleTopology X.smallEtaleTopology ⊣
        (Scheme.smallEtalePullback f).sheafPushforwardContinuous
          (Type v) Y.smallEtaleTopology X.smallEtaleTopology)

end SetValued

section AbelianGroups

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Definition 59.36.1 (2): the inverse-image functor on additive-group-valued
small étale sheaves is left adjoint to the corresponding direct-image functor. -/
@[stacks 03Q0] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_sheafAdjunction f AddCommGrpCat.{w} :
      (Scheme.smallEtalePullback f).sheafPullback
        AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology ⊣
        (Scheme.smallEtalePullback f).sheafPushforwardContinuous
          AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology)

end AbelianGroups
