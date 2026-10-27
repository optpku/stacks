/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Tensor and local module morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The commutative presentation of a native tensor is the transported module tensor. -/
private def tensorPresentation (A F : Modules X) :
    (toCommModules X).obj A ⊗ (toCommModules X).obj F ≅
      (toCommModules X).obj (A ⊗ F) :=
  (commModulesEquivalence X).unitIso.app
    ((toCommModules X).obj A ⊗ (toCommModules X).obj F)

/-- A native tensor morphism determines a pointwise bilinear map after sheafification. -/
private def tensorBilinear {A F G : Modules X} (φ : A ⊗ F ⟶ G) :
    PresheafOfModules.BilinearMap (commStructureSheaf X).obj
      ((toCommModules X).obj A).val ((toCommModules X).obj F).val
      ((toCommModules X).obj G).val :=
  PresheafOfModules.BilinearMap.ofHom
    (moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf X) _ ≫
      ((ModuleSheafification.tensorObjIso (commStructureSheaf X)
        ((toCommModules X).obj A) ((toCommModules X).obj F)).inv ≫
        (tensorPresentation A F).hom ≫ (toCommModules X).map φ).val)

/-- The actual small atlas of arrows into a chart. -/
private abbrev sliceBasis (U : smallEtaleSite X) :=
  CostructuredArrow.toOver
    (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U

/-- Restriction of a module to the small atlas of a slice. -/
private abbrev sliceRestriction (F : Modules X) (U : smallEtaleSite X) :=
  (PresheafOfModules.pushforward₀ (sliceBasis U) ((commRingSheaf X).over U).obj).obj
    (((toCommModules X).obj F).over U).val

set_option maxHeartbeats 2000000 in
/-- On a small slice chart, partial evaluation gives a linear map in the tensor's right input. -/
private def curryApp {A F G : Modules X} (φ : A ⊗ F ⟶ G) (U : smallEtaleSite X)
    (x : ((toCommModules X).obj A).val.obj (op U))
    (V : (CostructuredArrow
      (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U)ᵒᵖ) :
    (sliceRestriction F U).obj V ⟶ (sliceRestriction G U).obj V :=
  ModuleCat.ofHom (X := (sliceRestriction F U).obj V)
    (Y := (sliceRestriction G U).obj V)
    ((tensorBilinear φ).app (op ((sliceBasis U).obj V.unop).left)
    (((toCommModules X).obj A).val.map ((sliceBasis U).obj V.unop).hom.op x))

/-- Postcomposition is functorial, and partial tensor evaluation commutes with slice restriction. -/
theorem functor_laws :
    (∀ F G : Modules X, post F (𝟙 G) = 𝟙 (obj F G)) ∧
    (∀ (F : Modules X) {G H I : Modules X} (g : G ⟶ H) (h : H ⟶ I),
      post F (g ≫ h) = post F g ≫ post F h) ∧
    (∀ {A F G : Modules X} (φ : A ⊗ F ⟶ G) (U : smallEtaleSite X)
      (x : ((toCommModules X).obj A).val.obj (op U))
      {V W : (CostructuredArrow
        (PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)) U)ᵒᵖ}
      (i : V ⟶ W),
      (sliceRestriction F U).map i ≫
        (ModuleCat.restrictScalars (((commRingSheaf X).over U).obj.map
          ((sliceBasis U).op.map i)).hom).map (curryApp φ U x W) =
      curryApp φ U x V ≫ (sliceRestriction G U).map i) := sorry

/-- Internal Hom is covariant in its target by postcomposition of local morphisms. -/
def functor (F : Modules X) : Modules X ⥤ Modules X where
  obj := obj F
  map := post F
  map_id G := functor_laws.1 F G
  map_comp g h := functor_laws.2.1 F g h

/-- Partial tensor evaluation, viewed as a small code for a local module morphism. -/
private def currySection {A F G : Modules X} (φ : A ⊗ F ⟶ G) (U : smallEtaleSite X)
    (x : ((toCommModules X).obj A).val.obj (op U)) : Section F G U where
  app := curryApp φ U x
  naturality i := functor_laws.2.2 φ U x i

/-- Additivity and scalar compatibility of small-code partial evaluation. -/
private def curryLinearLaws : Prop :=
  (∀ {A F G : Modules X} (φ : A ⊗ F ⟶ G) (U : smallEtaleSite X)
      (x y : ((toCommModules X).obj A).val.obj (op U)),
    (currySection φ U (x + y) : sectionModule F G U) =
      currySection φ U x + currySection φ U y) ∧
  (∀ {A F G : Modules X} (φ : A ⊗ F ⟶ G) (U : smallEtaleSite X)
      (r : (commStructureSheaf X).obj.obj (op U))
      (x : ((toCommModules X).obj A).val.obj (op U)),
    (currySection φ U (r • x) : sectionModule F G U) =
      @SMul.smul _ _ (sectionModule F G U).isModule.toSMul r (currySection φ U x))

/-- Small-code partial evaluation bundled as a linear map of section modules. -/
private def curryLinear (h : curryLinearLaws (X := X)) {A F G : Modules X}
    (φ : A ⊗ F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ) :
    ((toCommModules X).obj A).val.obj U ⟶ (presheaf F G).obj U :=
  ModuleCat.ofHom (X := ((toCommModules X).obj A).val.obj U)
    (Y := (presheaf F G).obj U)
    { toFun := currySection φ U.unop
      map_add' := h.1 φ U.unop
      map_smul' := h.2 φ U.unop }

/-- Linearity and restriction compatibility of small-code partial evaluation. -/
private def curryLaws : Prop :=
  curryLinearLaws (X := X) ∧
  ∀ (h : curryLinearLaws (X := X)) {A F G : Modules X} (φ : A ⊗ F ⟶ G)
      {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V),
    ((toCommModules X).obj A).val.map i ≫
      (ModuleCat.restrictScalars ((commRingSheaf X).obj.map i).hom).map
        (curryLinear h φ V) =
      curryLinear h φ U ≫ (presheaf F G).map i

/-- Currying a tensor morphism using its actual small-atlas partial evaluations. -/
private def curryOf (h : curryLaws (X := X)) {A F G : Modules X} (φ : A ⊗ F ⟶ G) :
    A ⟶ obj F G :=
  (commModulesEquivalence X).counitIso.inv.app A ≫
    (ofCommModules X).map
      { val :=
          { app := curryLinear h.1 φ
            naturality := h.2 h.1 φ } }

/-- Evaluation of a local morphism at the identity arrow of its slice. -/
private def uncurryValue {A F G : Modules X} (φ : A ⟶ obj F G)
    (U : (smallEtaleSite X)ᵒᵖ) (x : ((toCommModules X).obj A).val.obj U)
    (y : ((toCommModules X).obj F).val.obj U) : ((toCommModules X).obj G).val.obj U :=
  ((sectionsEquiv F G U.unop (φ.val.app U x)).val.app (op (Over.mk (𝟙 U.unop)))) y

/-- Bilinearity and restriction compatibility of identity-slice evaluation. -/
private def uncurryLaws : Prop :=
  (∀ {A F G : Modules X} (φ : A ⟶ obj F G) (U : (smallEtaleSite X)ᵒᵖ)
      (x : ((toCommModules X).obj A).val.obj U)
      (y z : ((toCommModules X).obj F).val.obj U),
    uncurryValue φ U x (y + z) = uncurryValue φ U x y + uncurryValue φ U x z) ∧
  (∀ {A F G : Modules X} (φ : A ⟶ obj F G) (U : (smallEtaleSite X)ᵒᵖ)
      (x : ((toCommModules X).obj A).val.obj U)
      (r : (commStructureSheaf X).obj.obj U) (y : ((toCommModules X).obj F).val.obj U),
    uncurryValue φ U x (r • y) = r • uncurryValue φ U x y) ∧
  (∀ {A F G : Modules X} (φ : A ⟶ obj F G) (U : (smallEtaleSite X)ᵒᵖ)
      (x z : ((toCommModules X).obj A).val.obj U)
      (y : ((toCommModules X).obj F).val.obj U),
    uncurryValue φ U (x + z) y = uncurryValue φ U x y + uncurryValue φ U z y) ∧
  (∀ {A F G : Modules X} (φ : A ⟶ obj F G) (U : (smallEtaleSite X)ᵒᵖ)
      (r : (commStructureSheaf X).obj.obj U)
      (x : ((toCommModules X).obj A).val.obj U) (y : ((toCommModules X).obj F).val.obj U),
    uncurryValue φ U (r • x) y = r • uncurryValue φ U x y) ∧
  (∀ {A F G : Modules X} (φ : A ⟶ obj F G)
      {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
      (x : ((toCommModules X).obj A).val.obj U) (y : ((toCommModules X).obj F).val.obj U),
    ((toCommModules X).obj G).val.map i (uncurryValue φ U x y) =
      uncurryValue φ V (((toCommModules X).obj A).val.map i x)
        (((toCommModules X).obj F).val.map i y))

/-- The bilinear section pairing obtained by identity-slice evaluation. -/
private def uncurryBilinear (h : uncurryLaws (X := X)) {A F G : Modules X}
    (φ : A ⟶ obj F G) :
    PresheafOfModules.BilinearMap (commStructureSheaf X).obj
      ((toCommModules X).obj A).val ((toCommModules X).obj F).val
      ((toCommModules X).obj G).val where
  app U :=
    { toFun := fun x =>
        { toFun := uncurryValue φ U x
          map_add' := h.1 φ U x
          map_smul' := h.2.1 φ U x }
      map_add' := fun x z => LinearMap.ext (h.2.2.1 φ U x z)
      map_smul' := fun r x => LinearMap.ext (h.2.2.2.1 φ U r x) }
  naturality := h.2.2.2.2 φ

/-- Uncurrying by the pointwise tensor universal property and native sheafification. -/
private def uncurryOf (h : uncurryLaws (X := X)) {A F G : Modules X}
    (φ : A ⟶ obj F G) : A ⊗ F ⟶ G :=
  (commModulesEquivalence X).counitIso.inv.app (A ⊗ F) ≫
    (ofCommModules X).map
      ((tensorPresentation A F).inv ≫
        (ModuleSheafification.tensorObjIso (commStructureSheaf X)
          ((toCommModules X).obj A) ((toCommModules X).obj F)).hom ≫
        (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf X)).map
          (uncurryBilinear h φ).toHom ≫
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf X)
          ((toCommModules X).obj G)).hom) ≫
    (commModulesEquivalence X).counitIso.hom.app G

/-- Partial evaluation and identity-slice evaluation are inverse and natural. -/
private def curryingLaws : Prop :=
  curryLaws (X := X) ∧ uncurryLaws (X := X) ∧
  ∀ (hc : curryLaws (X := X)) (hu : uncurryLaws (X := X)),
    (∀ {A F G : Modules X} (φ : A ⊗ F ⟶ G),
      uncurryOf hu (curryOf hc φ) = φ) ∧
    (∀ {A F G : Modules X} (φ : A ⟶ obj F G),
      curryOf hc (uncurryOf hu φ) = φ) ∧
    (∀ {F A A' G : Modules X} (a : A' ⟶ A) (φ : A ⟶ obj F G),
      uncurryOf hu (a ≫ φ) = (tensorRight F).map a ≫ uncurryOf hu φ) ∧
    (∀ {F A G G' : Modules X} (φ : A ⊗ F ⟶ G) (g : G ⟶ G'),
      curryOf hc (φ ≫ g) = curryOf hc φ ≫ post F g)

/-- Small-atlas currying and evaluation satisfy the tensor–Hom inverse and naturality laws. -/
theorem homEquiv_laws : curryingLaws (X := X) := sorry

/-- Currying from a fixed-right module tensor into the sheaf of local morphisms. -/
def curry {A F G : Modules X} (φ : A ⊗ F ⟶ G) : A ⟶ obj F G :=
  curryOf homEquiv_laws.1 φ

/-- Evaluation uncurries a map into the sheaf of local module morphisms. -/
def uncurry {A F G : Modules X} (φ : A ⟶ obj F G) : A ⊗ F ⟶ G :=
  uncurryOf homEquiv_laws.2.1 φ

/-- Morphisms from a fixed-right module tensor correspond to local-morphism sheaf maps. -/
def homEquiv (F A G : Modules X) : (A ⊗ F ⟶ G) ≃ (A ⟶ obj F G) where
  toFun := curry
  invFun := uncurry
  left_inv := (homEquiv_laws.2.2 homEquiv_laws.1 homEquiv_laws.2.1).1
  right_inv := (homEquiv_laws.2.2 homEquiv_laws.1 homEquiv_laws.2.1).2.1

/-- Tensoring on the right by a module is left adjoint to its local-morphism sheaf functor. -/
def adjunction (F : Modules X) : tensorRight F ⊣ functor F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv F
      homEquiv_naturality_left_symm :=
        (homEquiv_laws.2.2 homEquiv_laws.1 homEquiv_laws.2.1).2.2.1
      homEquiv_naturality_right :=
        (homEquiv_laws.2.2 homEquiv_laws.1 homEquiv_laws.2.1).2.2.2 }

end AlgebraicGeometry.AlgebraicSpace.Modules.InternalHom
