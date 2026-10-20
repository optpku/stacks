/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {U X V Y : Scheme.{u}}
variable (j' : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
variable [Etale j] [Etale j']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Base change of a represented étale object commutes with restriction in a
cartesian square. The two arrows are the pullback lifts in opposite
directions. -/
def etaleRestrictionPullbackIso (h_cart : IsPullback j' g f j) :
    etaleRestriction j ⋙ smallEtalePullback f ≅
      smallEtalePullback g ⋙ etaleRestriction j' :=
  NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk
    { hom := pullback.lift
        (pullback.fst ((etaleRestriction j).obj W).hom f)
        (h_cart.lift (pullback.snd ((etaleRestriction j).obj W).hom f)
          (pullback.fst ((etaleRestriction j).obj W).hom f ≫ W.hom) (by sorry))
        (by sorry)
      inv := pullback.lift (pullback.fst W.hom g)
        (pullback.snd W.hom g ≫ j') (by sorry)
      hom_inv_id := by sorry
      inv_hom_id := by sorry } (by sorry)) (by sorry)

/-- Restriction followed by base change is continuous. -/
instance etaleRestrictionPullback_isContinuous :
    (etaleRestriction j ⋙ smallEtalePullback f).IsContinuous
      V.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (etaleRestriction j) (smallEtalePullback f)
    V.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- Base change followed by restriction is continuous. -/
instance smallEtalePullbackRestriction_isContinuous :
    (smallEtalePullback g ⋙ etaleRestriction j').IsContinuous
      V.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (smallEtalePullback g) (etaleRestriction j')
    V.smallEtaleTopology U.smallEtaleTopology X.smallEtaleTopology

/-- Restriction of small-étale direct image across a cartesian square,
constructed by applying presheaves to the pullback comparison. -/
def etaleAbelianPushforwardRestrictionIso (h_cart : IsPullback j' g f j) :
    etaleAbelianPushforward f ⋙ etaleRestrictionSheaf j AddCommGrpCat.{u} ≅
      etaleRestrictionSheaf j' AddCommGrpCat.{u} ⋙ etaleAbelianPushforward g :=
  Functor.sheafPushforwardContinuousIso
    (etaleRestrictionPullbackIso j' g f j h_cart) AddCommGrpCat.{u}
    V.smallEtaleTopology X.smallEtaleTopology

variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The adjunction comparison `j_! g_* ⟶ f_* j'_!`. It is the transpose
of the extension-by-zero unit followed by the cartesian restriction
comparison. Finiteness is needed only to prove that this map is invertible. -/
def abelianExtensionByZeroFinitePushforwardComparison
    (h_cart : IsPullback j' g f j) :
    etaleAbelianPushforward g ⋙ abelianExtensionByZero j ⟶
      abelianExtensionByZero j' ⋙ etaleAbelianPushforward f where
  app F := ((abelianExtensionByZero_adjunction j).homEquiv _ _).symm
    ((etaleAbelianPushforward g).map
        ((abelianExtensionByZero_adjunction j').unit.app F) ≫
      (etaleAbelianPushforwardRestrictionIso j' g f j h_cart).inv.app
        ((abelianExtensionByZero j').obj F))
  naturality := by sorry

/-- The restriction of the comparison, after the adjunction unit, is its
defining transpose. -/
theorem abelianExtensionByZeroFinitePushforwardComparison_unit
    (h_cart : IsPullback j' g f j)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianExtensionByZero_adjunction j).unit.app
        ((etaleAbelianPushforward g).obj F) ≫
      (etaleRestrictionSheaf j AddCommGrpCat.{u}).map
        ((abelianExtensionByZeroFinitePushforwardComparison j' g f j h_cart).app F) =
      (etaleAbelianPushforward g).map
          ((abelianExtensionByZero_adjunction j').unit.app F) ≫
        (etaleAbelianPushforwardRestrictionIso j' g f j h_cart).inv.app
          ((abelianExtensionByZero j').obj F) :=
  ((abelianExtensionByZero_adjunction j).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- For finite `f` and an open immersion `j`, the canonical comparison
between extension by zero and direct image is an isomorphism. -/
theorem abelianExtensionByZero_comp_etaleAbelianPushforward
    [IsFinite f] [IsOpenImmersion j]
    (h_cart : IsPullback j' g f j) :
    IsIso (abelianExtensionByZeroFinitePushforwardComparison j' g f j h_cart) :=
  sorry

/-- For a cartesian square with finite `f` and open immersion `j`, the
objectwise comparison identifies `f_* (j'_! F)` with `j_! (g_* F)`. -/
theorem abelianExtensionByZero_comp_etaleAbelianPushforward_app
    [IsFinite f] [IsOpenImmersion j]
    (h_cart : IsPullback j' g f j)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((abelianExtensionByZeroFinitePushforwardComparison j' g f j h_cart).app F) :=
  sorry

end AlgebraicGeometry.Scheme
