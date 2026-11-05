/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

/-!
# Proper morphisms: compact-support direct image equals pushforward
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- Every section of the small-étale pushforward along a proper morphism has
proper support over the base. -/
theorem hasProperSupport_of_isProper
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasProperSupport f F V σ := by
  change IsProper
    ((Scheme.IdealSheafData.vanishingIdeal
        (abelianSheafSectionSupport F ((smallEtalePullback f).obj V) σ)).subschemeι ≫
      CategoryTheory.Limits.pullback.fst V.hom f)
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance
    (MorphismProperty.pullback_fst V.hom f (inferInstance : IsProper f))

/-- For a proper morphism, the inverse of the compact-support inclusion keeps
the section and records that its support is proper. -/
def etaleLowerShriekProperInv :
    etaleAbelianPushforward f ⟶ etaleLowerShriek f where
  app F := ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := fun σ ↦ ⟨σ, hasProperSupport_of_isProper f F V.unop σ⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := by
        intro V W g
        apply ConcreteCategory.hom_ext
        intro σ
        rfl }
  naturality := by
    intro F G α
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- The comparison isomorphism `f_! ≅ f_*` for a proper morphism of schemes.
Its inverse sends a section to itself with its proper-support proof. -/
def etaleLowerShriekIso :
    etaleLowerShriek f ≅ etaleAbelianPushforward f where
  hom := etaleLowerShriekι f
  inv := etaleLowerShriekProperInv f
  hom_inv_id := by
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro σ
    rfl

/-- The canonical inclusion of compact-support direct image into small-étale
pushforward along a proper scheme morphism is an isomorphism. -/
instance etaleLowerShriekι_isIso : IsIso (etaleLowerShriekι f) :=
  (etaleLowerShriekIso f).isIso_hom

/-- The proper comparison has the original compact-support inclusion as its
forward map. -/
@[simp] theorem etaleLowerShriekIso_hom :
    (etaleLowerShriekIso f).hom = etaleLowerShriekι f := rfl

/-- The inverse proper comparison leaves the underlying section unchanged. -/
@[simp] theorem etaleLowerShriekIso_inv_app_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    (((etaleLowerShriekIso f).inv.app F).hom.app (op V) σ).val = σ := rfl

end AlgebraicGeometry.Scheme.Etale

end
