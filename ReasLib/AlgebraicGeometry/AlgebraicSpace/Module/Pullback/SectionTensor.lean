/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionComparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Base change of schemes étale over `Z` along `f ≫ g` identifies with base change
along `g` followed by spaces-étale pullback along `f`. -/
def etaleBaseChangeComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ spacesEtalePullback f :=
  (smallEtaleInclusion_comp_spacesEtalePullback (f ≫ g)).symm ≪≫
    isoWhiskerLeft (smallEtaleToSpaces Z) (spacesEtalePullbackComp f g) ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback g) (spacesEtalePullback f)

/-- `pullbackCompIso` is the left-adjoint mate of `pushforwardComp`. -/
theorem pullbackCompIso_eq {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompIso f g =
      Adjunction.leftAdjointCompIso
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Transport a morphism out of a commutative tensor product to `Y.Modules`. -/
def modulesTensorHom {Y : AlgebraicSpace S} {F G H : Y.Modules}
    (φ : (Modules.toCommModules Y).obj F ⊗ (Modules.toCommModules Y).obj G ⟶
      (Modules.toCommModules Y).obj H) : F ⊗ G ⟶ H :=
  (Modules.ofCommModules Y).map φ ≫
    (Modules.commModulesEquivalence Y).counitIso.hom.app H

/-- The type-valued sheaf underlying an `𝒪`-module. -/
abbrev moduleUnderlying {Y : AlgebraicSpace S} (M : Y.Modules) :
    Sheaf (smallEtaleTopology Y) (Type u) :=
  (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj M

/-- Charts of `Z ×_Y V` in the small étale site of `Z`. -/
abbrev pushforwardCharts {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (V : smallEtaleSite Y) :=
  StructuredArrow (op ((etaleBaseChange h).obj V)) (smallEtaleToSpaces Z).op

/-- Restriction of scalars along `commRingSheafIso` does not change the section carrier. -/
theorem toCommModules_val_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    ((Modules.toCommModules Y).obj M).val.obj U = M.val.obj U :=
  sorry

/-- View a module section as a section of its commutative presentation. -/
def asCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    ((Modules.toCommModules Y).obj M).val.obj U :=
  eqToHom (toCommModules_val_obj M U).symm s

/-- View a commutative presentation section as a section of the original module. -/
def ofCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : ((Modules.toCommModules Y).obj M).val.obj U) :
    M.val.obj U :=
  eqToHom (toCommModules_val_obj M U) s

/-- The spaces-étale extension of the type-valued sheaf underlying an `𝒪_Z`-module. -/
def moduleSpacesPushforward {Z : AlgebraicSpace S} (M : Z.Modules) :
    Sheaf (spacesEtaleTopology Z) (Type u) :=
  (EtaleTopos.extension Z).obj (moduleUnderlying M)

/-- Sections of the spaces-étale extension of `M` at `Z ×_Y V`. -/
def moduleSpacesSectionAt {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) : Type u :=
  (moduleSpacesPushforward M).obj.obj (op ((etaleBaseChange h).obj V))

/-- Forget module structure on a pushed-forward section at a small-étale object of `Y`. -/
def modulePushforwardForgetSection {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y)
    (s : ((Modules.pushforward h).obj M).val.obj (op V)) :
    ((typePushforward h).obj (moduleUnderlying M)).obj.obj (op V) :=
  ((RingedSite.ToposHom.ModulePushforward.forgetIso
      (ringedToposHom h)).hom.app M).hom.app (op V) s

/-- Direct-image evaluation and the specified spaces sheaf use the same actual
small-chart extension, so their section comparison is the identity. -/
def typePushforwardEvalIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) :
    ((typePushforward h).obj (moduleUnderlying M)).obj.obj (op V) ≅
      moduleSpacesSectionAt h M V :=
  Iso.refl _

/-- Chartwise sections at `Z ×_Y V` are spaces-étale sections of the extension. -/
theorem moduleSpacesSectionAt_eq {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) :
    moduleSpacesSectionAt h M V =
      (moduleSpacesPushforward M).obj.obj (op ((etaleBaseChange h).obj V)) :=
  sorry

/-- Reidentify a forgotten `h_* M` section at `V` as a spaces-étale section at `Z ×_Y V`. -/
def modulePushforwardSpacesSection {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y)
    (s : ((Modules.pushforward h).obj M).val.obj (op V)) :
    moduleSpacesSectionAt h M V :=
  (typePushforwardEvalIso h M V).hom (modulePushforwardForgetSection h M V s)

/-- Reidentify a spaces-étale section at `Z ×_Y V` as a forgotten `h_* M` section at `V`. -/
def modulePushforwardFromSpacesSection {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y)
    (t : moduleSpacesSectionAt h M V) :
    ((typePushforward h).obj (moduleUnderlying M)).obj.obj (op V) :=
  (typePushforwardEvalIso h M V).inv t

/-- The right Kan extension of the type-valued sheaf underlying an `𝒪_Z`-module. -/
abbrev moduleRan {Z : AlgebraicSpace S} (M : Z.Modules) :
    (spacesEtaleSite Z)ᵒᵖ ⥤ Type u :=
  EtaleTopos.fullChartExtension Z (moduleUnderlying M)

/-- Restrict a Kan-extended section along a structured arrow of the small étale inclusion. -/
def moduleRanRestrict {Z : AlgebraicSpace S} (M : Z.Modules)
    (W : spacesEtaleSite Z) (c : StructuredArrow (op W) (smallEtaleToSpaces Z).op)
    (t : (moduleRan M).obj (op W)) :
    (moduleRan M).obj ((smallEtaleToSpaces Z).op.obj c.right) :=
  (moduleRan M).map c.hom t

/-- Apply the Kan counit to recover a small-étale section. -/
def moduleRanCounitApp {Z : AlgebraicSpace S} (M : Z.Modules)
    (U : (smallEtaleSite Z)ᵒᵖ)
    (t : (moduleRan M).obj ((smallEtaleToSpaces Z).op.obj U)) :
    (moduleUnderlying M).obj.obj U :=
  (EtaleTopos.fullChartCounit Z (moduleUnderlying M)).app U t

/-- Restrict a spaces-étale extension section along a small-étale chart. -/
def moduleSpacesChartRestrict {Z : AlgebraicSpace S} (M : Z.Modules)
    (W : spacesEtaleSite Z) (c : StructuredArrow (op W) (smallEtaleToSpaces Z).op)
    (t : (moduleSpacesPushforward M).obj.obj (op W)) :
    (moduleUnderlying M).obj.obj c.right :=
  moduleRanCounitApp M c.right
    (moduleRanRestrict M W c
      ((EtaleTopos.extensionEvaluationIso Z (moduleUnderlying M) W).hom t))

/-- The type-valued underlying sheaf has the same sections as the module sheaf. -/
theorem moduleUnderlying_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (moduleUnderlying M).obj.obj U = M.val.obj U :=
  sorry

/-- Reidentify an underlying type-valued section as a module section. -/
def ofUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : (moduleUnderlying M).obj.obj U) :
    M.val.obj U :=
  eqToHom (moduleUnderlying_obj M U) s

/-- Reidentify a module section as an underlying type-valued section. -/
def toUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    (moduleUnderlying M).obj.obj U :=
  eqToHom (moduleUnderlying_obj M U).symm s

/-- Restrict a spaces-étale section of a pushed-forward module along a chart of `Z ×_Y V`. -/
def moduleSpacesChartRestrictPush {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) (c : pushforwardCharts h V)
    (t : moduleSpacesSectionAt h M V) :
    (moduleUnderlying M).obj.obj c.right :=
  moduleSpacesChartRestrict M ((etaleBaseChange h).obj V) c t

/-- Evaluate a pushed-forward module section at a small-étale chart of `Z ×_Y V`. -/
def moduleChartValue {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) (c : pushforwardCharts h V)
    (s : ((Modules.pushforward h).obj M).val.obj (op V)) :
    (moduleUnderlying M).obj.obj c.right :=
  moduleSpacesChartRestrictPush h M V c (modulePushforwardSpacesSection h M V s)

/-- Pure tensor of commutative presentations, transported to `toComm (M ⊗ N)`. -/
def commTensorSection {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((Modules.toCommModules Y).obj M).val.obj U)
    (y : ((Modules.toCommModules Y).obj N).val.obj U) :
    ((Modules.toCommModules Y).obj (M ⊗ N)).val.obj U :=
  (commTensorComparison M N).val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
        (PresheafOfModules.Monoidal.tensorObj
          ((Modules.toCommModules Y).obj M).val
          ((Modules.toCommModules Y).obj N).val)).app U
      (commPointwiseTensor U x y))

/-- `commTensorSection` is `commTensorComparison` applied to a pointwise pure tensor. -/
theorem commTensorSection_spec {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((Modules.toCommModules Y).obj M).val.obj U)
    (y : ((Modules.toCommModules Y).obj N).val.obj U) :
    commTensorSection M N x y =
      (commTensorComparison M N).val.app U
        ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
            (PresheafOfModules.Monoidal.tensorObj
              ((Modules.toCommModules Y).obj M).val
              ((Modules.toCommModules Y).obj N).val)).app U
          (commPointwiseTensor U x y)) :=
  sorry

/-- Pure tensor of chartwise evaluations, as a section of `M ⊗ N` on the chart. -/
def moduleChartTensor {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) (V : smallEtaleSite Y) (c : pushforwardCharts h V)
    (x : ((Modules.pushforward h).obj M).val.obj (op V))
    (y : ((Modules.pushforward h).obj N).val.obj (op V)) :
    (moduleUnderlying (M ⊗ N)).obj.obj c.right :=
  toUnderlyingSection (M ⊗ N)
    (ofCommSection (M ⊗ N)
      (commTensorSection M N
        (asCommSection M (ofUnderlyingSection M (moduleChartValue h M V c x)))
        (asCommSection N (ofUnderlyingSection N (moduleChartValue h N V c y)))))

/-- Cone of chartwise pure tensors presenting the pushforward-tensor comparison at `V`. -/
def pushforwardTensorCone {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) (V : smallEtaleSite Y)
    (x : ((Modules.pushforward h).obj M).val.obj (op V))
    (y : ((Modules.pushforward h).obj N).val.obj (op V)) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange h).obj V))
        (smallEtaleToSpaces Z).op ⋙ (moduleUnderlying (M ⊗ N)).obj) where
  pt := PUnit
  π :=
    { app := fun c => TypeCat.ofHom fun _ => moduleChartTensor h M N V c x y
      naturality := sorry }

/-- Assemble chartwise pure tensors to a section of `h_*(M ⊗ N)` at `V`. -/
def pushforwardTensorSection {Y Z : AlgebraicSpace S}
    (h : Z ⟶ Y) (M N : Z.Modules) (V : smallEtaleSite Y)
    (x : ((Modules.pushforward h).obj M).val.obj (op V))
    (y : ((Modules.pushforward h).obj N).val.obj (op V)) :
    ((Modules.pushforward h).obj (M ⊗ N)).val.obj (op V) :=
  ((RingedSite.ToposHom.ModulePushforward.forgetIso
      (ringedToposHom h)).inv.app (M ⊗ N)).hom.app (op V)
    (modulePushforwardFromSpacesSection h (M ⊗ N) V
      ((EtaleTopos.extensionEvaluationIso Z (moduleUnderlying (M ⊗ N))
          ((etaleBaseChange h).obj V)).inv
        (limit.lift _ (pushforwardTensorCone h M N V x y) PUnit.unit)))

/-- Compatible bilinear map of commutative presentations representing the
pushforward tensorator. -/
def pushforwardTensorBilinear {Y Z : AlgebraicSpace S}
    (h : Z ⟶ Y) (M N : Z.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheaf Y).obj
      ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj M)).val
      ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj N)).val
      ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj (M ⊗ N))).val where
  app V :=
    { toFun := fun x =>
        { toFun := fun y =>
            asCommSection ((Modules.pushforward h).obj (M ⊗ N))
              (pushforwardTensorSection h M N V.unop
                (ofCommSection ((Modules.pushforward h).obj M) x)
                (ofCommSection ((Modules.pushforward h).obj N) y))
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- The lax comparison `(h_* M) ⊗ (h_* N) ⟶ h_*(M ⊗ N)`, obtained by descending
the chartwise pure-tensor pairing of pushed-forward sections. -/
def pushforwardTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (M N : Z.Modules) :
    (Modules.pushforward h).obj M ⊗ (Modules.pushforward h).obj N ⟶
      (Modules.pushforward h).obj (M ⊗ N) :=
  modulesTensorHom
    (tensorHom
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj M))).inv
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj N))).inv ≫
      Functor.LaxMonoidal.μ
        (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
        ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj M)).val
        ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj N)).val ≫
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).map
        (PresheafOfModules.BilinearMap.toHom (pushforwardTensorBilinear h M N)) ≫
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj (M ⊗ N)))).hom)

/-- The oplax comparison `h^*(A ⊗ B) ⟶ h^* A ⊗ h^* B`, the adjunction transpose of the
tensor of units followed by `pushforwardTensorLax`. -/
def pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (Modules.pullback h).obj (A ⊗ B) ⟶
      (Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B :=
  ((Modules.pullbackPushforwardAdjunction h).homEquiv
      (A ⊗ B)
      ((Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B)).symm
    (((Modules.pullbackPushforwardAdjunction h).unit.app A ⊗ₘ
        (Modules.pullbackPushforwardAdjunction h).unit.app B) ≫
      pushforwardTensorLax h
        ((Modules.pullback h).obj A) ((Modules.pullback h).obj B))

/-- The chartwise tensor comparison agrees with the canonical pullback comparison. -/
theorem pullbackTensorOplax_eq {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    pullbackTensorOplax h A B = Modules.DirectTensorComparison.pullbackTensor h A B := sorry

/-- The pullback tensor comparison is an isomorphism with the canonical sectionwise inverse. -/
def pullbackTensorIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (Modules.pullback h).obj (A ⊗ B) ≅
      (Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B where
  hom := pullbackTensorOplax h A B
  inv := (Modules.PullbackTensor.tensorIso h A B).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The oplax pullback-tensor comparison is an isomorphism with the specified inverse. -/
instance instIsIso_pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (A B : Y.Modules) :
    IsIso (pullbackTensorOplax h A B) :=
  (pullbackTensorIso h A B).isIso_hom

/-- The lax comparison `h^* A ⊗ h^* B ⟶ h^*(A ⊗ B)` uses the actual section inverse
of the canonical tensor comparison. -/
def pullbackTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B ⟶
      (Modules.pullback h).obj (A ⊗ B) :=
  (pullbackTensorIso h A B).inv

/-- Pullback of the structure module along `h`. -/
def pullbackMonoidalUnitIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    (Modules.pullback h).obj (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit (structureSheaf Z) where
  hom := IdealSubobject.pullbackUnit h
  inv := Modules.structureModulePullbackInv h
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
