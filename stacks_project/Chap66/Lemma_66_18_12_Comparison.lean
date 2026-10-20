/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.EtaleBaseChange
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-! Compatibility checks for the canonical étale base-change comparisons. -/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
universe u
variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable (h_cart : IsPullback h f' f g) [Etale g] [Etale h]

#check (AlgebraicGeometry.AlgebraicSpace.pushforwardEtaleBaseChangeHom h_cart (Type (u + 1)) :
  ∀ F : Sheaf (smallEtaleTopology X) (Type (u + 1)),
    (etaleRestrictionSheaf g (Type (u + 1))).obj ((sheafPushforward (Type (u + 1)) f).obj F) ⟶
      (sheafPushforward (Type (u + 1)) f').obj ((etaleRestrictionSheaf h (Type (u + 1))).obj F))

-- Local instance justification (proof-local temporary data): the unique étaleness certificate
-- is determined by the cartesian square and its étale bottom edge.
#check (AlgebraicGeometry.AlgebraicSpace.isIso_pushforwardEtaleBaseChangeHom h_cart
    AddCommGrpCat.{u + 1} :
  ∀ F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1},
    -- Local instance justification (proof-local temporary data): this unique Prop certificate is determined by the cartesian square and its étale bottom edge and is needed to elaborate the comparison map.
    letI : Etale h := Etale.fst_of_isPullback h_cart
    IsIso (pushforwardEtaleBaseChangeHom h_cart AddCommGrpCat.{u + 1} F))
