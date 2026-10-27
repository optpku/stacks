/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent

/-!
# Small internal Hom for étale modules

Local morphisms are encoded by their values on a small model of the affine étale
charts. The range of this encoding supplies small section modules.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

namespace EtaleSheafHom

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- The affine étale chart represented by an object of the small model. -/
private abbrev chart (U : X.totalᵒᵖ)
    (c : SmallModel.{u} (X.p.obj U.unop).left.AffineEtale) :
    (X.p.obj U.unop).left.Etale :=
  (Scheme.AffineEtale.Spec _).obj ((equivSmallModel _).inverse.obj c)

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- The cartesian lift of an affine étale chart as an object of the slice. -/
private abbrev chartOver (U : X.totalᵒᵖ)
    (c : SmallModel.{u} (X.p.obj U.unop).left.AffineEtale) : Over U.unop :=
  Over.mk (smallEtaleEval_toBase U.unop (chart U c))

/-- Local module morphisms, with scalars acting on the target by local sections. -/
def localHomModule (F G : etaleModules X) (U : X.totalᵒᵖ) :
    ModuleCat.{u + 1} ((commEtaleStructureSheaf X).obj.obj U) :=
  @ModuleCat.of _ _ (F.over U.unop ⟶ G.over U.unop) inferInstance
    (Module.compHom _ (SheafOfModules.sectionAction (commEtaleStructureSheaf X) G U.unop))

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- Chartwise functions on sections, with scalars restricted from the base object. -/
def codeModule (F G : etaleModules X) (U : X.totalᵒᵖ) :
    ModuleCat.{u} ((commEtaleStructureSheaf X).obj.obj U) :=
  ModuleCat.of _ (∀ c : SmallModel.{u} (X.p.obj U.unop).left.AffineEtale,
    F.val.obj (op (chartOver U c).left) →
      (ModuleCat.restrictScalars
        ((commEtaleStructureSheaf X).obj.map (chartOver U c).hom.op).hom).obj
          (G.val.obj (op (chartOver U c).left)))

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- Evaluate a local morphism on every affine étale chart and every section. -/
def encodeFun (F G : etaleModules X) (U : X.totalᵒᵖ)
    (f : localHomModule F G U) : codeModule F G U :=
  fun c x => (f.val.app (op (chartOver U c))) x

/-- Chartwise evaluation preserves addition of local morphisms. -/
theorem encode_add (F G : etaleModules X) (U : X.totalᵒᵖ)
    (f g : localHomModule F G U) :
    encodeFun F G U (f + g) = encodeFun F G U f + encodeFun F G U g := sorry

/-- Chartwise evaluation commutes with multiplication by a local section. -/
theorem encode_smul (F G : etaleModules X) (U : X.totalᵒᵖ)
    (r : (commEtaleStructureSheaf X).obj.obj U) (f : localHomModule F G U) :
    encodeFun F G U (r • f) = r • encodeFun F G U f := sorry

/-- The linear map encoding local morphisms by chartwise evaluations. -/
def encode (F G : etaleModules X) (U : X.totalᵒᵖ) :
    localHomModule F G U →ₗ[(commEtaleStructureSheaf X).obj.obj U] codeModule F G U where
  toFun := encodeFun F G U
  map_add' := encode_add F G U
  map_smul' := encode_smul F G U

/-- The small module of chart codes arising from actual local morphisms. -/
def sectionModule (F G : etaleModules X) (U : X.totalᵒᵖ) :
    ModuleCat.{u} ((commEtaleStructureSheaf X).obj.obj U) :=
  ModuleCat.of _ (LinearMap.range (encode F G U))

/-- Recover a local morphism from its chart code by inversion on the range. -/
def decode (F G : etaleModules X) (U : X.totalᵒᵖ)
    (s : sectionModule F G U) : localHomModule F G U :=
  @Function.invFun (localHomModule F G U) (codeModule F G U) ⟨0⟩
    (encode F G U) s.val

/-- Finite presentation makes chartwise evaluation determine a local morphism. -/
theorem decode_encode (F G : etaleModules X) [F.IsFinitePresentation]
    (U : X.totalᵒᵖ) (f : localHomModule F G U) :
    decode F G U ((encode F G U).rangeRestrict f) = f := sorry

/-- Re-encoding the decoded local morphism recovers the original range code. -/
theorem encode_decode (F G : etaleModules X) (U : X.totalᵒᵖ)
    (s : sectionModule F G U) :
    (encode F G U).rangeRestrict (decode F G U s) = s := sorry

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- Evaluate a section code on a chart and a section of the source module. -/
def chartApply (F G : etaleModules X) (U : X.totalᵒᵖ)
    (s : sectionModule F G U)
    (c : SmallModel.{u} (X.p.obj U.unop).left.AffineEtale)
    (x : F.val.obj (op (chartOver U c).left)) : G.val.obj (op (chartOver U c).left) :=
  s.val c x

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- Canonical restriction of a local module morphism along a base arrow. -/
private def localRestrict (F G : etaleModules X) {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (f : localHomModule F G U) : localHomModule F G V :=
  (SheafOfModules.overFunctorMap (etaleStructureSheaf X) i.unop).inv.app F ≫
    (SheafOfModules.overMap (etaleStructureSheaf X) i.unop).map f ≫
      (SheafOfModules.overFunctorMap (etaleStructureSheaf X) i.unop).hom.app G

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- Restrict section codes by decoding, restricting the local morphism, and encoding. -/
def restrictFun (F G : etaleModules X) {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (s : sectionModule F G U) : sectionModule F G V :=
  (encode F G V).rangeRestrict (localRestrict F G i (decode F G U s))

/-- Restriction of section codes preserves addition. -/
theorem restrict_add (F G : etaleModules X) [F.IsFinitePresentation]
    {U V : X.totalᵒᵖ} (i : U ⟶ V) (s t : sectionModule F G U) :
    restrictFun F G i (s + t) = restrictFun F G i s + restrictFun F G i t := sorry

/-- Restriction of section codes is semilinear for structure-sheaf restriction. -/
theorem restrict_smul (F G : etaleModules X) [F.IsFinitePresentation]
    {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (r : (commEtaleStructureSheaf X).obj.obj U) (s : sectionModule F G U) :
    restrictFun F G i (r • s) =
      (commEtaleStructureSheaf X).obj.map i r • restrictFun F G i s := sorry

/-- The semilinear restriction map on the small section modules. -/
def restrict (F G : etaleModules X) [F.IsFinitePresentation]
    {U V : X.totalᵒᵖ} (i : U ⟶ V) :
    sectionModule F G U ⟶
      (ModuleCat.restrictScalars ((commEtaleStructureSheaf X).obj.map i).hom).obj
        (sectionModule F G V) :=
  ModuleCat.ofHom
    (X := sectionModule F G U)
    (Y := (ModuleCat.restrictScalars ((commEtaleStructureSheaf X).obj.map i).hom).obj
      (sectionModule F G V))
    { toFun := restrictFun F G i
      map_add' := restrict_add F G i
      map_smul' := restrict_smul F G i }

/-- Section-code restriction respects identity arrows. -/
theorem restrict_id (F G : etaleModules X) [F.IsFinitePresentation] (U : X.totalᵒᵖ) :
    restrict F G (𝟙 U) =
      (ModuleCat.restrictScalarsId' ((commEtaleStructureSheaf X).obj.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom ((commEtaleStructureSheaf X).obj.map_id U))).inv.app _ := sorry

/-- Section-code restriction respects composition and restriction of scalars. -/
theorem restrict_comp (F G : etaleModules X) [F.IsFinitePresentation]
    {U V W : X.totalᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    restrict F G (i ≫ j) =
      restrict F G i ≫
        (ModuleCat.restrictScalars ((commEtaleStructureSheaf X).obj.map i).hom).map (restrict F G j) ≫
          (ModuleCat.restrictScalarsComp' ((commEtaleStructureSheaf X).obj.map i).hom
            ((commEtaleStructureSheaf X).obj.map j).hom
            ((commEtaleStructureSheaf X).obj.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom ((commEtaleStructureSheaf X).obj.map_comp i j))).inv.app _ := sorry

/-- The module presheaf of small codes for local morphisms from a finitely presented module. -/
def presheaf (F G : etaleModules X) [F.IsFinitePresentation] :
    PresheafOfModules.{u} (etaleStructureSheaf X).obj where
  obj U := sectionModule F G U
  map i := restrict F G i
  map_id := restrict_id F G
  map_comp := restrict_comp F G

/-- The presheaf of small codes for local module morphisms satisfies the sheaf condition. -/
theorem presheaf_isSheaf (F G : etaleModules X) [F.IsFinitePresentation] :
    Presheaf.IsSheaf X.etaleTopology (presheaf F G).presheaf := sorry

end EtaleSheafHom

/-- The sheaf of local morphisms from a finitely presented étale module, with small sections. -/
def moduleSheafHomEtale (F G : etaleModules X) [F.IsFinitePresentation] : etaleModules X where
  val := EtaleSheafHom.presheaf F G
  isSheaf := EtaleSheafHom.presheaf_isSheaf F G

namespace EtaleSheafHom

/-- Sections of the small internal Hom identify with actual local module morphisms. -/
def sectionsEquiv (F G : etaleModules X) [F.IsFinitePresentation] (U : X.totalᵒᵖ) :
    (moduleSheafHomEtale F G).val.obj U ≃ (F.over U.unop ⟶ G.over U.unop) where
  toFun := decode F G U
  invFun := (encode F G U).rangeRestrict
  left_inv := encode_decode F G U
  right_inv := decode_encode F G U

-- Local declaration justification (metaprogramming implementation): keep chart and slice
-- restriction implementation names private while exposing their formulas in public definitions.
set_option backward.privateInPublic true in
/-- The section equivalence recovers the given chartwise evaluation. -/
theorem sectionsEquiv_apply_chart (F G : etaleModules X) [F.IsFinitePresentation]
    (U : X.totalᵒᵖ) (s : (moduleSheafHomEtale F G).val.obj U)
    (c : SmallModel.{u} (X.p.obj U.unop).left.AffineEtale)
    (x : F.val.obj (op (chartOver U c).left)) :
    ((sectionsEquiv F G U s).val.app (op (chartOver U c))) x =
      chartApply F G U s c x := sorry

/-- Restricting an internal-Hom section restricts its local module morphism canonically. -/
theorem sectionsEquiv_restrict (F G : etaleModules X) [F.IsFinitePresentation]
    {U V : X.totalᵒᵖ} (i : U ⟶ V) (s : (moduleSheafHomEtale F G).val.obj U) :
    sectionsEquiv F G V ((moduleSheafHomEtale F G).val.map i s) =
      (SheafOfModules.overFunctorMap (etaleStructureSheaf X) i.unop).inv.app F ≫
        (SheafOfModules.overMap (etaleStructureSheaf X) i.unop).map (sectionsEquiv F G U s) ≫
          (SheafOfModules.overFunctorMap (etaleStructureSheaf X) i.unop).hom.app G := sorry

end EtaleSheafHom

end AlgebraicGeometry.GroupoidsOver
