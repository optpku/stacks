/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Skyscraper
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Indiscrete

/-!
# Skyscraper module sheaves on ringed spaces

This module specializes the point-space and skyscraper-sheaf constructions to module sheaves over
the structure sheaf of a ringed space.

## API

- `AlgebraicGeometry.PointRingedSpace.Module` owns the equivalence between modules over a stalk
  ring and module sheaves on the associated one-point ringed space.
- `AlgebraicGeometry.RingedSpace.Module.Skyscraper` owns skyscraper module sheaves on the ambient
  ringed space, their specialization maps, and the point-pullback adjunction.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}

open CategoryTheory.Limits

/-- Restriction of scalars along `PointRingedSpace.ringTopIso x` identifies stalk modules with
modules over the value of the point-space structure sheaf on its top open. -/
public noncomputable def PointRingedSpace.Module.topEquivalence (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) ≌
      ModuleCat.{u} ((pointRingCatSheaf x).obj.obj (op (⊤ : Opens (TopCat.of PUnit)))) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (PointRingedSpace.ringTopIso x).ringCatIsoToRingEquiv

/-- The object part of the module presheaf on `pointRingedSpace x` associated to a stalk module
`M`: it is `M` on the unique nonempty open and the terminal module on the empty open. -/
public noncomputable def PointRingedSpace.Module.presheafObj
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (U : (Opens (TopCat.of PUnit))ᵒᵖ) →
    ModuleCat.{u} ((pointRingCatSheaf x).obj.obj U) :=
  fun U ↦ by
    classical
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (pointOpen_eq_top hU)
      subst hU'
      exact
        (ModuleCat.restrictScalars (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M
    · exact ⊤_ ModuleCat.{u} ((pointRingCatSheaf x).obj.obj U)

/-- On the top open of the one-point space,
`PointRingedSpace.Module.presheafObj x M` is the stalk module `M` with scalars restricted along the canonical
identification of the top ring with `RingCat.of (X.presheaf.stalk x)`. -/
theorem PointRingedSpace.Module.presheafObj_op_top
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    PointRingedSpace.Module.presheafObj x M (op (⊤ : Opens (TopCat.of PUnit))) =
      (ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M := sorry

/-- On the bottom open of the one-point space,
`PointRingedSpace.Module.presheafObj x M` is the terminal module. -/
private theorem PointRingedSpace.Module.presheafObj_op_bot
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    PointRingedSpace.Module.presheafObj x M (op (⊥ : Opens (TopCat.of PUnit))) =
      ⊤_ ModuleCat.{u} ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit)))) := sorry

/-- The restriction map of the point-module presheaf is the explicit
top-branch restriction-of-scalars map, and otherwise the zero map into the terminal bottom value.
-/
public noncomputable def PointRingedSpace.Module.presheafMap
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    {U V : (Opens (TopCat.of PUnit))ᵒᵖ} (i : U ⟶ V) :
    PointRingedSpace.Module.presheafObj x M U ⟶
      (ModuleCat.restrictScalars ((pointRingCatSheaf x).obj.map i).hom).obj
        (PointRingedSpace.Module.presheafObj x M V) := by
  classical
  by_cases hV : PUnit.unit ∈ unop V
  · have hU : PUnit.unit ∈ unop U := i.unop.le hV
    have hU' : U = op ⊤ := by
      simpa using congrArg op (pointOpen_eq_top hU)
    have hV' : V = op ⊤ := by
      simpa using congrArg op (pointOpen_eq_top hV)
    subst hU'
    subst hV'
    have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
    exact
      (ModuleCat.restrictScalarsId'
        ((pointRingCatSheaf x).obj.map i).hom
        (by
          subst hi
          exact congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_id (op ⊤)))).inv.app
        (PointRingedSpace.Module.presheafObj x M (op ⊤))
  · simpa [PointRingedSpace.Module.presheafObj, hV] using
      (0 :
        PointRingedSpace.Module.presheafObj x M U ⟶
          (ModuleCat.restrictScalars
            ((pointRingCatSheaf x).obj.map i).hom).obj
              (PointRingedSpace.Module.presheafObj x M V))

/-
Mathlib provides the canonical topological skyscraper sheaf and the canonical pushforward of
module sheaves, but it does not package the intermediate equivalence between stalk modules and
module sheaves on a one-point ringed space. We retain the explicit top/bottom module values and
restriction maps above, isolate only their functoriality and sheaf conditions as proof obligations,
package top-open evaluation as that missing equivalence, and use its forward functor as the input
to the canonical `RingedSpace.Hom.pushforward`. This keeps all non-Prop data explicit while
avoiding a parallel pushforward construction.
-/

/-- The explicit restriction maps of the point-module presheaf preserve identities. -/
theorem PointRingedSpace.Module.presheafMap_id
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (U : (Opens (TopCat.of PUnit))ᵒᵖ) :
    PointRingedSpace.Module.presheafMap x M (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((pointRingCatSheaf x).obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_id U))).inv.app
          (PointRingedSpace.Module.presheafObj x M U) := sorry
/- Proof strategy: split according to whether `PUnit.unit ∈ unop U`; use `pointOpen_eq_top`
and the identity restriction-of-scalars comparison on the top branch, and uniqueness of maps into
the terminal module on the bottom branch. -/

/-- The explicit restriction maps of the point-module presheaf preserve composition. -/
theorem PointRingedSpace.Module.presheafMap_comp
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    {U V W : (Opens (TopCat.of PUnit))ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    PointRingedSpace.Module.presheafMap x M (i ≫ j) =
      PointRingedSpace.Module.presheafMap x M i ≫
        (ModuleCat.restrictScalars ((pointRingCatSheaf x).obj.map i).hom).map
          (PointRingedSpace.Module.presheafMap x M j) ≫
        (ModuleCat.restrictScalarsComp'
          ((pointRingCatSheaf x).obj.map i).hom
          ((pointRingCatSheaf x).obj.map j).hom
          ((pointRingCatSheaf x).obj.map (i ≫ j)).hom
          (congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_comp i j))).inv.app
            (PointRingedSpace.Module.presheafObj x M W) := sorry
/- Proof strategy: split according to whether `PUnit.unit ∈ unop W`; the bottom branch follows
from terminality, while in the top branch all three opens are `⊤` and the goal reduces to
`ModuleCat.restrictScalarsComp'` for identity maps. -/

/-- The presheaf of modules on `pointRingedSpace x` with value `M` on its unique nonempty open and
the terminal module on the empty open. -/
noncomputable def PointRingedSpace.Module.presheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    PresheafOfModules.{u} (pointRingCatSheaf x).obj where
  obj := PointRingedSpace.Module.presheafObj x M
  map := PointRingedSpace.Module.presheafMap x M
  map_id := PointRingedSpace.Module.presheafMap_id x M
  map_comp := PointRingedSpace.Module.presheafMap_comp x M

/-- The explicit point-module presheaf satisfies the sheaf condition on the one-point space. -/
theorem PointRingedSpace.Module.presheaf_isSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of PUnit))
      (PointRingedSpace.Module.presheaf x M).presheaf := sorry
/- Proof strategy: apply `TopCat.Presheaf.isSheaf_on_punit_of_isTerminal`; after unfolding
`PointRingedSpace.Module.presheaf`, identify the bottom-open value with the terminal module and use that the
forgetful functor to `AddCommGrpCat` preserves terminal objects. -/

/-- The sheaf of modules on `pointRingedSpace x` corresponding to the stalk module `M`. -/
noncomputable def PointRingedSpace.Module.sheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} (RingedSpace.ringCatSheaf (pointRingedSpace x)) where
  val := PointRingedSpace.Module.presheaf x M
  isSheaf := PointRingedSpace.Module.presheaf_isSheaf x M

/-- The value of `PointRingedSpace.Module.sheaf x M` on the top open is canonically the scalar restriction
of the stalk module `M` along the defining identification of the point-space structure ring. -/
public noncomputable def PointRingedSpace.Module.topValueIso
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (PointRingedSpace.Module.sheaf x M).val.obj (op (⊤ : Opens (TopCat.of PUnit))) ≅
      (PointRingedSpace.Module.topEquivalence x).functor.obj M :=
  eqToIso (PointRingedSpace.Module.presheafObj_op_top x M)

/-- Specialization of `SheafOfModules.Indiscrete.homEquivTop` to morphisms into the point module
sheaf associated to `M`. -/
public noncomputable abbrev PointRingedSpace.Module.homEquivTop
    (x : X) (G : (pointRingedSpace x).Modules)
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :=
  SheafOfModules.Indiscrete.homEquivTop G (PointRingedSpace.Module.sheaf x M)

/-- Evaluating the point-module specialization is literal evaluation on the top open. -/
@[simp]
theorem PointRingedSpace.Module.homEquivTop_apply
    (x : X) (G : (pointRingedSpace x).Modules)
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (f : G ⟶ PointRingedSpace.Module.sheaf x M) :
    PointRingedSpace.Module.homEquivTop x G M f = f.val.app (op ⊤) := sorry

/-- A stalk module determines functorially its canonical module sheaf on the one-point ringed
space `pointRingedSpace x`. -/
public noncomputable def PointRingedSpace.Module.functor
    (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) ⥤ (pointRingedSpace x).Modules where
  obj M := PointRingedSpace.Module.sheaf x M
  map {M N} φ :=
    (PointRingedSpace.Module.homEquivTop x (PointRingedSpace.Module.sheaf x M) N).symm
      ((PointRingedSpace.Module.topValueIso x M).hom ≫
        (PointRingedSpace.Module.topEquivalence x).functor.map φ ≫
        (PointRingedSpace.Module.topValueIso x N).inv)
  map_id := sorry
  map_comp := sorry

/-- The top-open component of `PointRingedSpace.Module.functor.map φ` is the scalar restriction of `φ`
under the canonical top-open identifications. -/
@[simp]
theorem PointRingedSpace.Module.functor_map_app_top
    (x : X) {M N : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))} (φ : M ⟶ N) :
    ((PointRingedSpace.Module.functor x).map φ).val.app (op ⊤) ≫
        (PointRingedSpace.Module.topValueIso x N).hom =
      (PointRingedSpace.Module.topValueIso x M).hom ≫
        (PointRingedSpace.Module.topEquivalence x).functor.map φ := sorry

/-- Evaluating a module sheaf on `pointRingedSpace x` at the top open and transporting scalars
back along `PointRingedSpace.ringTopIso x` gives its corresponding stalk module. -/
public noncomputable def PointRingedSpace.Module.topSectionsFunctor
    (x : X) :
    (pointRingedSpace x).Modules ⥤
      ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) :=
  SheafOfModules.evaluation
      (R := pointRingCatSheaf x) (op (⊤ : Opens (TopCat.of PUnit))) ⋙
    (PointRingedSpace.Module.topEquivalence x).inverse

/-- The component at a stalk module of the canonical unit identifying it with the top-open
sections of its associated point module sheaf. -/
public noncomputable def PointRingedSpace.Module.unitIsoApp
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    M ≅
      (PointRingedSpace.Module.topSectionsFunctor x).obj
        ((PointRingedSpace.Module.functor x).obj M) :=
  (PointRingedSpace.Module.topEquivalence x).unitIso.app M ≪≫
    ((PointRingedSpace.Module.topEquivalence x).inverse.mapIso
      (PointRingedSpace.Module.topValueIso x M)).symm

/-- The unit components for top-open evaluation are natural in the stalk module. -/
theorem PointRingedSpace.Module.unitIsoApp_naturality
    (x : X) {M N : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))}
    (φ : M ⟶ N) :
    φ ≫ (PointRingedSpace.Module.unitIsoApp x N).hom =
      (PointRingedSpace.Module.unitIsoApp x M).hom ≫
        (PointRingedSpace.Module.topSectionsFunctor x).map
          ((PointRingedSpace.Module.functor x).map φ) := sorry

/-- The identity on stalk modules is naturally isomorphic to first forming the point module
sheaf and then taking its top-open sections. -/
public noncomputable def PointRingedSpace.Module.unitIso (x : X) :
    𝟭 (ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) ≅
      PointRingedSpace.Module.functor x ⋙ PointRingedSpace.Module.topSectionsFunctor x :=
  NatIso.ofComponents
    (PointRingedSpace.Module.unitIsoApp x)
    (PointRingedSpace.Module.unitIsoApp_naturality x)

/-- The component at a point-space module sheaf of the canonical counit reconstructed from its
top-open value. -/
public noncomputable def PointRingedSpace.Module.counitIsoApp
    (x : X) (G : (pointRingedSpace x).Modules) :
    (PointRingedSpace.Module.functor x).obj
        ((PointRingedSpace.Module.topSectionsFunctor x).obj G) ≅
      G :=
  SheafOfModules.Indiscrete.isoOfTop _ G
    (PointRingedSpace.Module.topValueIso x
        ((PointRingedSpace.Module.topSectionsFunctor x).obj G) ≪≫
      (PointRingedSpace.Module.topEquivalence x).counitIso.app
        (G.val.obj (op (⊤ : Opens (TopCat.of PUnit)))))

/-- The counit components reconstructed from top-open evaluation are natural in the point-space
module sheaf. -/
theorem PointRingedSpace.Module.counitIsoApp_naturality
    (x : X) {G H : (pointRingedSpace x).Modules} (f : G ⟶ H) :
    (PointRingedSpace.Module.functor x).map
          ((PointRingedSpace.Module.topSectionsFunctor x).map f) ≫
        (PointRingedSpace.Module.counitIsoApp x H).hom =
      (PointRingedSpace.Module.counitIsoApp x G).hom ≫ f := sorry

/-- Taking top-open sections and then forming the associated point module sheaf is naturally
isomorphic to the identity on module sheaves over `pointRingedSpace x`. -/
public noncomputable def PointRingedSpace.Module.counitIso (x : X) :
    PointRingedSpace.Module.topSectionsFunctor x ⋙ PointRingedSpace.Module.functor x ≅
      𝟭 ((pointRingedSpace x).Modules) :=
  NatIso.ofComponents
    (PointRingedSpace.Module.counitIsoApp x)
    (PointRingedSpace.Module.counitIsoApp_naturality x)

/-- The unit and counit for point module sheaves satisfy the forward triangle identity. -/
theorem PointRingedSpace.Module.functor_unitIso_comp
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (PointRingedSpace.Module.functor x).map
          ((PointRingedSpace.Module.unitIso x).hom.app M) ≫
        (PointRingedSpace.Module.counitIso x).hom.app
          ((PointRingedSpace.Module.functor x).obj M) =
      𝟙 ((PointRingedSpace.Module.functor x).obj M) := sorry

/-- Modules over the stalk ring at `x` are canonically equivalent to module sheaves on the
one-point ringed space `pointRingedSpace x`; the inverse is evaluation on the top open. -/
public noncomputable def PointRingedSpace.Module.equivalence (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) ≌
      (pointRingedSpace x).Modules where
  functor := PointRingedSpace.Module.functor x
  inverse := PointRingedSpace.Module.topSectionsFunctor x
  unitIso := PointRingedSpace.Module.unitIso x
  counitIso := PointRingedSpace.Module.counitIso x
  functor_unitIso_comp := PointRingedSpace.Module.functor_unitIso_comp x

/-- The pullback model of the module-stalk functor at `x`: pull a module sheaf back along
`pointInclusion x`, then identify module sheaves on the resulting one-point ringed space with
modules over `X.presheaf.stalk x`. -/
public noncomputable def RingedSpace.Module.pointPullbackFunctor (x : X) :
    X.Modules ⥤ ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) :=
  RingedSpace.Hom.pullback (pointInclusion x) ⋙
    PointRingedSpace.Module.topSectionsFunctor x

/-- The pullback model of the module-stalk functor is additive. -/
@[stacks 0FKS "additivity of the point-pullback module functor"]
noncomputable instance RingedSpace.Module.pointPullbackFunctor_additive (x : X) :
    (RingedSpace.Module.pointPullbackFunctor x).Additive := sorry

/-- Forming the module sheaf on `pointRingedSpace x` associated to a stalk module is an
equivalence of categories. -/
noncomputable instance PointRingedSpace.Module.functor_isEquivalence (x : X) :
    (PointRingedSpace.Module.functor x).IsEquivalence :=
  (PointRingedSpace.Module.equivalence x).isEquivalence_functor

/-- Sending a stalk module to its point module sheaf and then pushing forward along
`pointInclusion x` is the skyscraper-module functor at `x`. -/
public noncomputable def RingedSpace.Module.Skyscraper.functor
    (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) ⥤ X.Modules :=
  PointRingedSpace.Module.functor x ⋙ RingedSpace.Hom.pushforward (pointInclusion x)

/-- The pullback model of the module-stalk functor at `x` is left adjoint to the
skyscraper-module functor at `x`. -/
public noncomputable def RingedSpace.Module.Skyscraper.adjunction (x : X) :
    RingedSpace.Module.pointPullbackFunctor x ⊣ RingedSpace.Module.Skyscraper.functor x :=
  (SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom (pointInclusion x))).comp
    (PointRingedSpace.Module.equivalence x).symm.toAdjunction

/-- For a point `x : X` and a module `M` over the stalk ring at `x`,
`RingedSpace.Module.Skyscraper.atPoint x M` is the canonical pushforward along
`pointInclusion x : pointRingedSpace x ⟶ X`. -/
noncomputable def RingedSpace.Module.Skyscraper.atPoint
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} ((RingedSpace.ringCatSheaf X)) :=
  (RingedSpace.Module.Skyscraper.functor x).obj M

/-- The additive group underlying a module used as the value of a skyscraper module sheaf. -/
noncomputable abbrev RingedSpace.Module.Skyscraper.value
    {X : RingedSpace.{u}} {x : X}
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) AddCommGrpCat.{u}).obj M

/-- The canonical additive map from the value module of a skyscraper module sheaf to its stalk at
an arbitrary point, obtained by taking the germ of the global section determined by that value. -/
public noncomputable def RingedSpace.Module.Skyscraper.valueToStalk
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) (x' : X) :
    RingedSpace.Module.Skyscraper.value M ⟶
      TopCat.Presheaf.stalk (RingedSpace.Module.Skyscraper.atPoint x M).val.presheaf x' :=
  (forget₂
      (ModuleCat.{u}
        ((pointRingCatSheaf x).obj.obj (op (⊤ : Opens (TopCat.of PUnit)))))
      AddCommGrpCat.{u}).map (PointRingedSpace.Module.topValueIso x M).inv ≫
    TopCat.Presheaf.germ (RingedSpace.Module.Skyscraper.atPoint x M).val.presheaf ⊤ x' trivial

/-- Along a specialization `x ⤳ x'`, the value-to-stalk map is linear after restricting scalars
from `X.presheaf.stalk x` to `X.presheaf.stalk x'`. -/
theorem RingedSpace.Module.Skyscraper.valueToStalk_map_smul
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x')
    (r : X.presheaf.stalk x') (m : M) :
    RingedSpace.Module.Skyscraper.valueToStalk x M x'
        (X.presheaf.stalkSpecializes h r • m) =
      r • RingedSpace.Module.Skyscraper.valueToStalk x M x' m := sorry

/-- The value-to-stalk map bundled as a linear map over the stalk ring at a specialization of the
support point. -/
public noncomputable def RingedSpace.Module.Skyscraper.valueToStalkLinearMap
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x') :
    ((ModuleCat.restrictScalars
      (X.presheaf.stalkSpecializes h).hom).obj M) →ₗ[
        X.presheaf.stalk x']
      RingedSpace.stalkModuleCat (RingedSpace.Module.Skyscraper.atPoint x M) x' where
  toFun := RingedSpace.Module.Skyscraper.valueToStalk x M x'
  map_add' := (RingedSpace.Module.Skyscraper.valueToStalk x M x').hom.map_add
  map_smul' := RingedSpace.Module.Skyscraper.valueToStalk_map_smul x M h

/-- The canonical map from the scalar restriction of the value module to the stalk of its
skyscraper module sheaf at a specialization of the support point. -/
public noncomputable def RingedSpace.Module.Skyscraper.stalkMapOfSpecializes
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x') :
    (ModuleCat.restrictScalars
        (X.presheaf.stalkSpecializes h).hom).obj M ⟶
      RingedSpace.stalkModuleCat (RingedSpace.Module.Skyscraper.atPoint x M) x' :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u} (X.presheaf.stalk x'))
    (RingedSpace.Module.Skyscraper.valueToStalkLinearMap x M h)

/-- At a specialization of its support point, a skyscraper module sheaf has stalk canonically
isomorphic to its value module with scalars restricted along the specialization map of stalk
rings. -/
instance RingedSpace.Module.Skyscraper.stalkMapOfSpecializes_isIso
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x') :
    IsIso (RingedSpace.Module.Skyscraper.stalkMapOfSpecializes x M h) := sorry

/-- Away from the specializations of its support point, the stalk of a skyscraper module sheaf is
the zero module over the ambient stalk ring. -/
theorem RingedSpace.Module.Skyscraper.stalk_isZero_of_notSpecializes
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : ¬x ⤳ x') :
    IsZero (RingedSpace.stalkModuleCat (RingedSpace.Module.Skyscraper.atPoint x M) x') := sorry

/-- An `X.Modules` object is a skyscraper module sheaf if it is isomorphic to
`RingedSpace.Module.Skyscraper.atPoint x M` for some point `x : X` and some module `M` over the stalk ring. -/
def RingedSpace.Module.IsSkyscraper
    (ℱ : SheafOfModules.{u} ((RingedSpace.ringCatSheaf X))) : Prop :=
  ∃ (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))),
    IsIsomorphic ℱ (RingedSpace.Module.Skyscraper.atPoint x M)

end

end AlgebraicGeometry
