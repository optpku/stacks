/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.EtaleRootsPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NormalizedYonedaTrace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualCompactificationChange
variable {U C D : Scheme.{u}}
variable (j : U ⟶ C) (j' : U ⟶ D) (f : D ⟶ C)
variable [IsOpenImmersion j] [IsOpenImmersion j']
variable (hcart : IsPullback (𝟙 U) j' j f)

include hcart in
/-- The interior cartesian square commutes after precomposition with V. -/
theorem site_condition (V : U.Etale) :
    (𝟙 V.left) ≫ (V.hom ≫ j) = (V.hom ≫ j') ≫ f := sorry

/-- The explicit site map embeds V into its cartesian pullback by identity
on V and its given map to the second compactification. -/
def siteMap (V : U.Etale) :
    (etaleRestriction j').obj V ⟶ ((etaleRestriction j ⋙ smallEtalePullback f).obj V) := by
  let w := site_condition j j' f hcart V
  let p : V.left ⟶ pullback (V.hom ≫ j) f := pullback.lift (𝟙 V.left) (V.hom ≫ j') w
  exact MorphismProperty.Over.homMk p (pullback.lift_snd _ _ w)

include hcart in
/-- The cartesian interior square makes this specified site map invertible. -/
instance siteMap_isIso (V : U.Etale) : IsIso (siteMap j j' f hcart V) := sorry

def siteIso : etaleRestriction j' ≅ etaleRestriction j ⋙ smallEtalePullback f :=
  NatIso.ofComponents (fun V ↦ asIso (siteMap j j' f hcart V)) (fun _ ↦ sorry)

/-- On direct images, the comparison is restriction of sections along the
actual site isomorphism above. -/
def restrictionIso :
    (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        C.smallEtaleTopology D.smallEtaleTopology ⋙
      etaleRestrictionSheaf j AddCommGrpCat.{u + 1} ≅
    etaleRestrictionSheaf j' AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun F ↦
    { hom := ObjectProperty.homMk
        { app := fun V ↦ F.obj.map ((siteIso j j' f hcart).hom.app V.unop).op
          naturality := sorry }
      inv := ObjectProperty.homMk
        { app := fun V ↦ F.obj.map ((siteIso j j' f hcart).inv.app V.unop).op
          naturality := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }) (fun _ ↦ sorry)

variable [HasSheafify C.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify D.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : C.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback f).op.HasLeftKanExtension F]

abbrev pullbackFunctor := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
  C.smallEtaleTopology D.smallEtaleTopology

/-- Inverse image commutes with extension by zero through the actual adjoint
mate of restriction along the cartesian interior square. -/
def extensionIso : etaleExtensionByZero j AddCommGrpCat.{u + 1} ⋙ pullbackFunctor f ≅
    etaleExtensionByZero j' AddCommGrpCat.{u + 1} :=
  (((etaleExtensionByZero_adjunction j AddCommGrpCat.{u + 1}).comp
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        C.smallEtaleTopology D.smallEtaleTopology)).ofNatIsoRight
      (restrictionIso j j' f hcart)).leftAdjointUniq
    (etaleExtensionByZero_adjunction j' AddCommGrpCat.{u + 1})

variable [HasExt.{u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf D.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Cohomological compactification-change map: exact pullback of the Yoneda
class, the canonical integer-sheaf unit, then the extension-by-zero mate. -/
def cohomologyMap (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F).H i →+
      ((etaleExtensionByZero j' AddCommGrpCat.{u + 1}).obj F).H i where
  toFun x := Sheaf.H.map ((extensionIso j j' f hcart).hom.app F) i
    ((Ext.mk₀ (ActualEtaleRootsPullback.constantAddSheafPullbackIso f).inv).comp
      (x.mapExactFunctor (pullbackFunctor f)) (zero_add i))
  map_zero' := sorry
  map_add' := sorry

variable [hproper : IsProper f]
include hproper in
/-- Proper base change gives invariance for this specified compactification
map: f is an isomorphism on the cartesian open interior, and both extensions
vanish on the boundary. No arbitrary cohomology isomorphism is assumed. -/
theorem cohomologyMap_bijective (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ V : U.Etaleᵒᵖ, ∀ s : F.obj.obj V, IsOfFinAddOrder s) (i : ℕ) :
    Function.Bijective (cohomologyMap j j' f hcart F i) := sorry

def cohomologyEquiv (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ V : U.Etaleᵒᵖ, ∀ s : F.obj.obj V, IsOfFinAddOrder s) (i : ℕ) :
    ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj F).H i ≃+
      ((etaleExtensionByZero j' AddCommGrpCat.{u + 1}).obj F).H i :=
  AddEquiv.ofBijective (cohomologyMap j j' f hcart F i)
    (cohomologyMap_bijective j j' f hcart F hF i)

end ActualCompactificationChange
