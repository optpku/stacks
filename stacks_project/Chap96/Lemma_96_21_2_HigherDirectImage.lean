/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap96.Lemma_96_17_6_LowerShriek
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

/-!
# Higher direct images on associated τ-sites

The underived pushforward `f_*` of a 1-morphism of categories fibred in groupoids
is the cocontinuous sheaf pushforward of the cartesian total functor on each
associated `τ`-site. Higher direct images are the right derived functors of that
pushforward on abelian sheaves and on sheaves of modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ConcreteCategory Functor Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageFunctor`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Pointwise right Kan extensions along the opposite cartesian total functor exist on
abelian presheaves. -/
instance toCartesianBasedFunctor_op_hasPointwiseRightKanExtension_addCommGrpCat
    {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P :=
  sorry

/-- The underived abelian pushforward `f_*` on associated `τ`-sites. -/
abbrev abelianPushforward {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)

/-- `abelianPushforward f τ` is the cocontinuous sheaf pushforward of the cartesian
total functor. -/
theorem abelianPushforward_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    abelianPushforward f τ =
      (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ) :=
  rfl

/-- Cocontinuous abelian pushforward on associated `τ`-sites is additive. -/
instance abelianPushforward_additive {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (abelianPushforward f τ).Additive :=
  sorry

/-- Sheaves of modules on an associated `τ`-site form an abelian category. -/
instance associatedModules_abelian {𝒳 : GroupoidsOver S} {σ : StandardTopology} :
    Abelian (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)) :=
  RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u} (associatedRingedSite 𝒳 σ)

/-- Associated `τ`-module sheaves admit injective resolutions. -/
instance associatedModules_hasInjectiveResolutions {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    HasInjectiveResolutions (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)) :=
  sorry

/-- Forgetting module structure on an associated `τ`-site preserves homology. -/
instance associatedToSheaf_preservesHomology {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).PreservesHomology :=
  sorry

/-- Forgetting module structure on an associated `τ`-site preserves injective objects. -/
instance associatedToSheaf_preservesInjectiveObjects {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).PreservesInjectiveObjects :=
  sorry

/-- Forgetting module structure on an associated `τ`-site is additive. -/
instance associatedToSheaf_additive {𝒳 : GroupoidsOver S} {σ : StandardTopology} :
    (SheafOfModules.toSheaf (associatedStructureSheaf 𝒳 σ)).Additive :=
  sorry

variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [Abelian (SheafOfModules.{u + 1} (X.associatedStructureSheaf τ))]
variable [Abelian (SheafOfModules.{u + 1} (Y.associatedStructureSheaf τ))]
variable [HasInjectiveResolutions
    (SheafOfModules.{u + 1} (X.associatedStructureSheaf τ))]

/-- The degree-`i` higher direct image functor `R^i f_*` on abelian sheaves. -/
abbrev higherDirectImageFunctor (i : ℕ) :
    Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (abelianPushforward f τ).rightDerived i

/-- The degree-`i` higher direct image `R^i f_* F` of an abelian sheaf. -/
abbrev higherDirectImage (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (i : ℕ) :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (higherDirectImageFunctor f τ i).obj F

/-- `higherDirectImage f τ F i` is the object map of `rightDerived` of abelian
pushforward. -/
theorem higherDirectImage_eq (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    (i : ℕ) :
    higherDirectImage f τ F i = ((abelianPushforward f τ).rightDerived i).obj F :=
  rfl

/-- The ring homomorphism `O_Y(y) ⟶ O_X(x)` attached to a structured arrow for the
cartesian total functor of `f`. -/
def modulePushforwardRingHom (y : Y.totalᵒᵖ)
    (s : StructuredArrow y (toCartesianBasedFunctor f).toFunctor.op) :
    (associatedStructureSheaf Y τ).obj.obj y ⟶
      (associatedStructureSheaf X τ).obj.obj s.right :=
  (associatedStructureSheaf Y τ).obj.map s.hom ≫
    (associatedStructureSheafInverseImageIso_cartesian f τ).hom.hom.app s.right

/-- The underlying abelian group of `f_* G` at `y`. -/
abbrev modulePushforwardObjAbelian
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ) :
    AddCommGrpCat.{u + 1} :=
  ((abelianPushforward f τ).obj
      ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G)).obj.obj y

/-- Scalar multiplication by a section of `O_Y` on the underlying abelian group of
`f_* G` at `y`, obtained by acting on the right Kan extension cone. -/
def modulePushforwardSmulHom
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ)
    (r : (associatedStructureSheaf Y τ).obj.obj y) :
    modulePushforwardObjAbelian f τ G y ⟶ modulePushforwardObjAbelian f τ G y :=
  let L := (toCartesianBasedFunctor f).toFunctor.op
  let P := ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G).obj
  let e := L.ranObjObjIsoLimit P y
  let D := StructuredArrow.proj y L ⋙ P
  limit.lift D
      { pt := (L.ran.obj P).obj y
        π :=
          { app := fun s ↦
              e.hom ≫
                limit.π D s ≫
                  (G.val.obj s.right).smul ((modulePushforwardRingHom f τ y s).hom r)
            naturality := sorry } } ≫
    e.inv

/-- The `O_Y(y)`-module structure on the underlying abelian group of `f_* G` at `y`. -/
instance modulePushforwardObjModule
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ) :
    Module ((associatedStructureSheaf Y τ).obj.obj y)
      (modulePushforwardObjAbelian f τ G y) where
  smul r a := (modulePushforwardSmulHom f τ G y r).hom a
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The value of the underived module pushforward at an object of `Y`. -/
def modulePushforwardObj
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ) :
    ModuleCat.{u + 1} ((associatedStructureSheaf Y τ).obj.obj y) :=
  ModuleCat.of _ (modulePushforwardObjAbelian f τ G y)

/-- Restriction maps of underived module pushforward, as the abelian cocontinuous
restriction maps. -/
def modulePushforwardMap
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) {y y' : Y.totalᵒᵖ}
    (β : y ⟶ y') :
    modulePushforwardObj f τ G y ⟶
      (ModuleCat.restrictScalars
          ((associatedStructureSheaf Y τ).obj.map β).hom).obj
        (modulePushforwardObj f τ G y') :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun :=
        (((abelianPushforward f τ).obj
              ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G)).obj.map
            β).hom
      map_add' :=
        map_add
          (((abelianPushforward f τ).obj
                ((SheafOfModules.toSheaf (associatedStructureSheaf X τ)).obj G)).obj.map
              β).hom
      map_smul' := sorry }

/-- The underived module pushforward as a presheaf of modules. -/
def modulePushforwardPresheaf
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    PresheafOfModules.{u + 1} (associatedStructureSheaf Y τ).obj where
  obj y := modulePushforwardObj f τ G y
  map β := modulePushforwardMap f τ G β
  map_id := sorry
  map_comp := sorry

/-- The underived module pushforward `f_*` on associated `τ`-sites, landing in
`SheafOfModules.{u + 1}`. -/
def modulePushforward :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) where
  obj G :=
    { val := modulePushforwardPresheaf f τ G
      isSheaf := sorry }
  map {G G'} φ :=
    { val :=
        { app := fun y ↦
            ConcreteCategory.ofHom (C := ModuleCat _)
              { toFun :=
                  (((abelianPushforward f τ).map
                        ((SheafOfModules.toSheaf
                            (associatedStructureSheaf X τ)).map φ)).hom.app
                      y).hom
                map_add' :=
                  map_add
                    (((abelianPushforward f τ).map
                          ((SheafOfModules.toSheaf
                              (associatedStructureSheaf X τ)).map φ)).hom.app
                        y).hom
                map_smul' := sorry }
          naturality := sorry } }
  map_id := sorry
  map_comp := sorry

/-- Cocontinuous module pushforward on associated `τ`-sites is additive. -/
instance modulePushforward_additive : (modulePushforward f τ).Additive :=
  sorry

/-- Module pushforward followed by forgetting module structure is additive. -/
instance modulePushforward_comp_toSheaf_additive :
    (modulePushforward f τ ⋙
      SheafOfModules.toSheaf (associatedStructureSheaf Y τ)).Additive :=
  sorry

/-- Forgetting module structure then applying abelian pushforward is additive. -/
instance toSheaf_comp_abelianPushforward_additive :
    (SheafOfModules.toSheaf (associatedStructureSheaf X τ) ⋙
      abelianPushforward f τ).Additive :=
  sorry

/-- Forgetting module structure after underived module pushforward recovers abelian
cocontinuous pushforward. -/
def modulePushforward_toSheafIso :
    modulePushforward f τ ⋙
        SheafOfModules.toSheaf (associatedStructureSheaf Y τ) ≅
      SheafOfModules.toSheaf (associatedStructureSheaf X τ) ⋙ abelianPushforward f τ :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          { hom :=
              { app := fun y ↦
                  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x ↦ x) sorry)
                naturality := sorry } }
        inv :=
          { hom :=
              { app := fun y ↦
                  AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x ↦ x) sorry)
                naturality := sorry } }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The degree-`i` higher direct image functor `R^i f_*` on sheaves of modules. -/
abbrev higherDirectImageModuleFunctor (i : ℕ) :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (modulePushforward f τ).rightDerived i

/-- The degree-`i` higher direct image `R^i f_* G` of a sheaf of modules. -/
abbrev higherDirectImageModule
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (i : ℕ) :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (higherDirectImageModuleFunctor f τ i).obj G

/-- `higherDirectImageModule f τ G i` is the object map of `rightDerived` of module
pushforward. -/
theorem higherDirectImageModule_eq
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (i : ℕ) :
    higherDirectImageModule f τ G i = ((modulePushforward f τ).rightDerived i).obj G :=
  rfl

end AlgebraicGeometry.GroupoidsOver
