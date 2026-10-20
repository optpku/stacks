/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Compactification
import StacksCheckRecall

/-!
# Compactification of underived étale lower shriek
-/

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.3.6 (1): Compact-support pushforward factors canonically through
extension by zero along an open immersion into a proper scheme. -/
@[stacks 0F52] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompactifyIso :
    ∀ {X Xbar Y : Scheme.{u}} (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
      [IsOpenImmersion j] [IsProper fbar]
      [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify Xbar.smallEtaleTopology AddCommGrpCat.{u}],
      etaleLowerShriek (j ≫ fbar) ≅
        abelianExtensionByZero j ⋙ etaleLowerShriek fbar)

/- Lemma 63.3.6 (2): For the proper structure morphism, compact-support
pushforward is ordinary pushforward, giving the second canonical identification. -/
@[stacks 0F52] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompactifyPushforwardIso :
    ∀ {X Xbar Y : Scheme.{u}} (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
      [IsOpenImmersion j] [IsProper fbar]
      [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify Xbar.smallEtaleTopology AddCommGrpCat.{u}],
      etaleLowerShriek (j ≫ fbar) ≅
        abelianExtensionByZero j ⋙ etaleAbelianPushforward fbar)
