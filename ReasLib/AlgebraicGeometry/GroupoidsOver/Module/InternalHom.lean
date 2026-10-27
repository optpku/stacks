/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InternalHom.Adjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Tensor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange

/-! # Internal Hom and topology comparison for fppf modules -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Finite presentation is preserved by restriction from the fppf topology to the étale topology. -/
instance restriction_isFinitePresentation [AlgebraicStack X]
    (F : fppfModules X) [F.IsFinitePresentation] :
    ((restriction X).obj F).IsFinitePresentation := sorry

/-- Local morphisms between fppf module sheaves form an fppf sheaf. -/
theorem moduleSheafHomFppf_isSheaf [AlgebraicStack X]
    (F G : fppfModules X) [F.IsFinitePresentation] :
    Presheaf.IsSheaf (fppfTopology X)
      ((PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheaf X)).obj
        (moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G)).val).presheaf :=
  sorry

/-- The fppf sheaf of local morphisms from a finitely presented module. -/
def moduleSheafHomFppf [AlgebraicStack X] (F G : fppfModules X)
    [F.IsFinitePresentation] : fppfModules X where
  val := (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheaf X)).obj
    (moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G)).val
  isSheaf := moduleSheafHomFppf_isSheaf F G

/-- The fppf internal Hom has the presheaf of local morphisms of the étale restrictions. -/
theorem moduleSheafHomFppf_eq [AlgebraicStack X] (F G : fppfModules X)
    [F.IsFinitePresentation] :
    (moduleSheafHomFppf F G).val =
      (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheaf X)).obj
        (moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G)).val := rfl

/-- The presheaf comparison identifying restriction of fppf internal Hom with étale internal Hom. -/
def moduleSheafHomRestrictionPresheafIso [AlgebraicStack X] (F G : fppfModules X)
    [F.IsFinitePresentation] :
    ((restriction X).obj (moduleSheafHomFppf F G)).val ≅
      (moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G)).val :=
  PresheafOfModules.Restriction.compComponentIso'
    (fppfToEtaleStructurePresheafIso X).inv (fppfToEtaleStructurePresheafIso X).hom
    (𝟙 _) (fppfToEtaleStructurePresheafIso X).inv_hom_id _ ≪≫
  (PresheafOfModules.Restriction.idComponentIso' (𝟙 _) rfl _).symm

/-- The canonical topology-comparison maps for internal Hom are mutually inverse. -/
theorem moduleSheafHom_restrictionIso_laws [AlgebraicStack X]
    (F G : fppfModules X) [F.IsFinitePresentation] :
    (moduleSheafHomRestrictionPresheafIso F G).hom ≫
        (moduleSheafHomRestrictionPresheafIso F G).inv = 𝟙 _ ∧
    (moduleSheafHomRestrictionPresheafIso F G).inv ≫
        (moduleSheafHomRestrictionPresheafIso F G).hom = 𝟙 _ := sorry

/-- Restriction of the fppf internal Hom is canonically the étale internal Hom. -/
def moduleSheafHom_restrictionIso [AlgebraicStack X] (F G : fppfModules X)
    [F.IsFinitePresentation] :
    (restriction X).obj (moduleSheafHomFppf F G) ≅
      moduleSheafHomEtale ((restriction X).obj F) ((restriction X).obj G) where
  hom := ⟨(moduleSheafHomRestrictionPresheafIso F G).hom⟩
  inv := ⟨(moduleSheafHomRestrictionPresheafIso F G).inv⟩
  hom_inv_id := SheafOfModules.hom_ext (moduleSheafHom_restrictionIso_laws F G).1
  inv_hom_id := SheafOfModules.hom_ext (moduleSheafHom_restrictionIso_laws F G).2

/-- Restricting scalars to the étale coefficient presheaf and back recovers an fppf presheaf. -/
def restrictionRoundtripPresheafIso (F : fppfModules X) :
    (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheaf X)).obj
      ((restriction X).obj F).val ≅ F.val :=
  PresheafOfModules.Restriction.compComponentIso'
    (fppfToEtaleStructurePresheafIso X).hom (fppfToEtaleStructurePresheafIso X).inv
    (𝟙 _) (fppfToEtaleStructurePresheafIso X).hom_inv_id F.val ≪≫
  (PresheafOfModules.Restriction.idComponentIso' (𝟙 _) rfl F.val).symm

/-- Recover an fppf-module morphism from the morphism of its étale restrictions. -/
def restrictionHomInv {F G : fppfModules X}
    (f : (restriction X).obj F ⟶ (restriction X).obj G) : F ⟶ G where
  val := (restrictionRoundtripPresheafIso F).inv ≫
    (PresheafOfModules.restrictScalars (fppfToEtaleStructurePresheaf X)).map f.val ≫
      (restrictionRoundtripPresheafIso G).hom

/-- Coefficient transport and its inverse are inverse on morphisms of fppf modules. -/
theorem restrictionHomEquiv_laws (F G : fppfModules X) :
    (∀ f : F ⟶ G, restrictionHomInv ((restriction X).map f) = f) ∧
    (∀ f : (restriction X).obj F ⟶ (restriction X).obj G,
      (restriction X).map (restrictionHomInv f) = f) := sorry

/-- Morphisms between fppf modules are the morphisms between their étale restrictions. -/
def restrictionHomEquiv (F G : fppfModules X) :
    (F ⟶ G) ≃ ((restriction X).obj F ⟶ (restriction X).obj G) where
  toFun := (restriction X).map
  invFun := restrictionHomInv
  left_inv := (restrictionHomEquiv_laws F G).1
  right_inv := (restrictionHomEquiv_laws F G).2

/-- The pure tensor section in the fppf tensor product. -/
def fppfTensorSection (H F : fppfModules X) (U : X.totalᵒᵖ)
    (x : H.val.obj U) (y : F.val.obj U) : (moduleTensorFppf H F).val.obj U :=
  (associatedModuleTensorIso ((toCommAssociatedModules X .fppf).obj H)
    ((toCommAssociatedModules X .fppf).obj F)).hom.val.app U
    ((@moduleSheafificationUnitToVal.{u + 1, u, u, u}
      X.total inferInstance (X.associatedTopology .fppf)
      (associatedTopology_hasSheafCompose_commRing X .fppf)
      (associatedTopology_hasWeakSheafify X .fppf) (associatedTopology_wEqualsLocallyBijective X .fppf)
      (commAssociatedStructureSheaf X .fppf)
      (PresheafOfModules.Monoidal.tensorObj
        ((toCommAssociatedModules X .fppf).obj H).val
        ((toCommAssociatedModules X .fppf).obj F).val)).app U (x ⊗ₜ y))

variable [AlgebraicStack X] (F G H : fppfModules X) [F.IsFinitePresentation]

/-- Evaluate a morphism into fppf internal Hom on a pair of sections. -/
def fppfHomUncurryFun (f : H ⟶ moduleSheafHomFppf F G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) (y : F.val.obj U) : G.val.obj U :=
  ((EtaleSheafHom.sectionsEquiv ((restriction X).obj F) ((restriction X).obj G) U
    ((f.val.app U) x)).val.app (op (Over.mk (𝟙 U.unop)))) y

/-- Bilinearity and restriction compatibility of local fppf internal-Hom evaluation. -/
def fppfHomUncurryLaws (f : H ⟶ moduleSheafHomFppf F G) : Prop :=
  (∀ U (x x' : ((toCommAssociatedModules X .fppf).obj H).val.obj U)
    (y : ((toCommAssociatedModules X .fppf).obj F).val.obj U),
    fppfHomUncurryFun F G H f U (x + x') y =
      fppfHomUncurryFun F G H f U x y + fppfHomUncurryFun F G H f U x' y) ∧
  (∀ U (r : (commAssociatedStructureSheaf X .fppf).obj.obj U)
    (x : ((toCommAssociatedModules X .fppf).obj H).val.obj U)
    (y : ((toCommAssociatedModules X .fppf).obj F).val.obj U),
    fppfHomUncurryFun F G H f U (r • x) y =
      r • (fppfHomUncurryFun F G H f U x y :
        ((toCommAssociatedModules X .fppf).obj G).val.obj U)) ∧
  (∀ U (x : ((toCommAssociatedModules X .fppf).obj H).val.obj U)
    (y y' : ((toCommAssociatedModules X .fppf).obj F).val.obj U),
    fppfHomUncurryFun F G H f U x (y + y') =
      fppfHomUncurryFun F G H f U x y + fppfHomUncurryFun F G H f U x y') ∧
  (∀ U (r : (commAssociatedStructureSheaf X .fppf).obj.obj U)
    (x : ((toCommAssociatedModules X .fppf).obj H).val.obj U)
    (y : ((toCommAssociatedModules X .fppf).obj F).val.obj U),
    fppfHomUncurryFun F G H f U x (r • y) =
      r • (fppfHomUncurryFun F G H f U x y :
        ((toCommAssociatedModules X .fppf).obj G).val.obj U)) ∧
  (∀ {U V} (i : U ⟶ V)
    (x : ((toCommAssociatedModules X .fppf).obj H).val.obj U)
    (y : ((toCommAssociatedModules X .fppf).obj F).val.obj U),
    ((toCommAssociatedModules X .fppf).obj G).val.map i
        (fppfHomUncurryFun F G H f U x y) =
      fppfHomUncurryFun F G H f V
        (((toCommAssociatedModules X .fppf).obj H).val.map i x)
        (((toCommAssociatedModules X .fppf).obj F).val.map i y))

/-- Uncurrying in fppf modules using the linearity and naturality laws of local evaluation. -/
def fppfHomUncurryWith (f : H ⟶ moduleSheafHomFppf F G)
    (h : fppfHomUncurryLaws F G H f) : moduleTensorFppf H F ⟶ G :=
  let b : PresheafOfModules.BilinearMap (commAssociatedStructureSheaf X .fppf).obj
      ((toCommAssociatedModules X .fppf).obj H).val ((toCommAssociatedModules X .fppf).obj F).val
      ((toCommAssociatedModules X .fppf).obj G).val :=
    { app U := LinearMap.mk₂ _ (fppfHomUncurryFun F G H f U)
        (h.1 U) (h.2.1 U) (h.2.2.1 U) (h.2.2.2.1 U)
      naturality := h.2.2.2.2 }
  (fromCommAssociatedModules X).map
    ((associatedModuleTensorIso ((toCommAssociatedModules X .fppf).obj H)
      ((toCommAssociatedModules X .fppf).obj F)).inv ≫
      (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
        X.total inferInstance (X.associatedTopology .fppf)
        (associatedTopology_hasSheafCompose_commRing X .fppf)
        (associatedTopology_hasWeakSheafify X .fppf) (associatedTopology_wEqualsLocallyBijective X .fppf)
        (commAssociatedStructureSheaf X .fppf)
        (PresheafOfModules.Monoidal.tensorObj
          ((toCommAssociatedModules X .fppf).obj H).val
          ((toCommAssociatedModules X .fppf).obj F).val)
        ((toCommAssociatedModules X .fppf).obj G)).symm b.toHom) ≫
    (QCoh.fromToCommAssociatedModulesIso G).hom

/-- Local evaluation of a tensor morphism after restricting the first section to a slice. -/
def fppfHomCurryLocalFun (g : moduleTensorFppf H F ⟶ G) (U : X.totalᵒᵖ)
    (x : H.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (y : (((restriction X).obj F).over U.unop).val.obj W) :
    (((restriction X).obj G).over U.unop).val.obj W :=
  (g.val.app (op W.unop.left))
    (fppfTensorSection H F (op W.unop.left) (H.val.map W.unop.hom.op x) y)

/-- Linearity and slice restriction compatibility of local fppf tensor evaluation. -/
def fppfHomCurryLocalLaws (g : moduleTensorFppf H F ⟶ G) : Prop :=
  ∀ (U : X.totalᵒᵖ) (x : H.val.obj U),
    (∀ W (y y' : (((restriction X).obj F).over U.unop).val.obj W),
      fppfHomCurryLocalFun F G H g U x W (y + y') =
        fppfHomCurryLocalFun F G H g U x W y + fppfHomCurryLocalFun F G H g U x W y') ∧
    (∀ W (r : ((etaleStructureSheaf X).over U.unop).obj.obj W)
      (y : (((restriction X).obj F).over U.unop).val.obj W),
      fppfHomCurryLocalFun F G H g U x W (r • y) =
        r • fppfHomCurryLocalFun F G H g U x W y) ∧
    (∀ {W W'} (i : W ⟶ W')
      (y : (((restriction X).obj F).over U.unop).val.obj W),
      (((restriction X).obj G).over U.unop).val.map i
          (fppfHomCurryLocalFun F G H g U x W y) =
        fppfHomCurryLocalFun F G H g U x W'
          ((((restriction X).obj F).over U.unop).val.map i y))

/-- The local morphism obtained by fixing the first section of a fppf tensor morphism. -/
def fppfHomCurryLocalWith (g : moduleTensorFppf H F ⟶ G)
    (h : fppfHomCurryLocalLaws F G H g) (U : X.totalᵒᵖ) (x : H.val.obj U) :
    ((restriction X).obj F).over U.unop ⟶ ((restriction X).obj G).over U.unop where
  val :=
    { app W := ModuleCat.ofHom
        (X := (((restriction X).obj F).over U.unop).val.obj W)
        (Y := (((restriction X).obj G).over U.unop).val.obj W)
        { toFun := fppfHomCurryLocalFun F G H g U x W
          map_add' := (h U x).1 W
          map_smul' := (h U x).2.1 W }
      naturality := fun {_ _} i => ModuleCat.hom_ext (LinearMap.ext
        (fun y => ((h U x).2.2 i y).symm)) }

/-- The section code of local fppf tensor evaluation. -/
def fppfHomCurryFunWith (g : moduleTensorFppf H F ⟶ G)
    (h : fppfHomCurryLocalLaws F G H g) (U : X.totalᵒᵖ) (x : H.val.obj U) :
    (moduleSheafHomFppf F G).val.obj U :=
  (EtaleSheafHom.encode ((restriction X).obj F) ((restriction X).obj G) U).rangeRestrict
    (fppfHomCurryLocalWith F G H g h U x)

/-- Linearity and restriction compatibility of encoded fppf currying. -/
def fppfHomCurryLaws (g : moduleTensorFppf H F ⟶ G)
    (h : fppfHomCurryLocalLaws F G H g) : Prop :=
  (∀ U (x x' : H.val.obj U),
    fppfHomCurryFunWith F G H g h U (x + x') =
      fppfHomCurryFunWith F G H g h U x + fppfHomCurryFunWith F G H g h U x') ∧
  (∀ U (r : (structureSheaf X).obj.obj U) (x : H.val.obj U),
    fppfHomCurryFunWith F G H g h U (r • x) =
      r • fppfHomCurryFunWith F G H g h U x) ∧
  (∀ {U V} (i : U ⟶ V) (x : H.val.obj U),
    (moduleSheafHomFppf F G).val.map i (fppfHomCurryFunWith F G H g h U x) =
      fppfHomCurryFunWith F G H g h V (H.val.map i x))

/-- Currying into fppf internal Hom using the laws of local evaluation and encoding. -/
def fppfHomCurryWith (g : moduleTensorFppf H F ⟶ G)
    (h : fppfHomCurryLocalLaws F G H g) (h' : fppfHomCurryLaws F G H g h) :
    H ⟶ moduleSheafHomFppf F G where
  val :=
    { app U := ModuleCat.ofHom
        (X := H.val.obj U) (Y := (moduleSheafHomFppf F G).val.obj U)
        { toFun := fppfHomCurryFunWith F G H g h U
          map_add' := h'.1 U
          map_smul' := h'.2.1 U }
      naturality := fun {_ _} i => ModuleCat.hom_ext (LinearMap.ext
        (fun x => (h'.2.2 i x).symm)) }

/-- Local evaluation and encoding satisfy linearity, naturality, and the currying inverse laws. -/
theorem moduleSheafHomFppf_homEquiv_laws :
    (∀ f, fppfHomUncurryLaws F G H f) ∧
    (∀ g, fppfHomCurryLocalLaws F G H g) ∧
    (∀ g (h : fppfHomCurryLocalLaws F G H g), fppfHomCurryLaws F G H g h) ∧
    (∀ (f : H ⟶ moduleSheafHomFppf F G) (h : fppfHomUncurryLaws F G H f)
      (k : fppfHomCurryLocalLaws F G H (fppfHomUncurryWith F G H f h))
      (k' : fppfHomCurryLaws F G H (fppfHomUncurryWith F G H f h) k),
      fppfHomCurryWith F G H (fppfHomUncurryWith F G H f h) k k' = f) ∧
    (∀ (g : moduleTensorFppf H F ⟶ G) (h : fppfHomCurryLocalLaws F G H g)
      (h' : fppfHomCurryLaws F G H g h)
      (k : fppfHomUncurryLaws F G H (fppfHomCurryWith F G H g h h')),
      fppfHomUncurryWith F G H (fppfHomCurryWith F G H g h h') k = g) := sorry

/-- Tensor morphisms in fppf modules correspond to morphisms into the fppf internal Hom. -/
def moduleSheafHomFppf_homEquiv :
    (H ⟶ moduleSheafHomFppf F G) ≃ (moduleTensorFppf H F ⟶ G) where
  toFun f := fppfHomUncurryWith F G H f ((moduleSheafHomFppf_homEquiv_laws F G H).1 f)
  invFun g := fppfHomCurryWith F G H g
    ((moduleSheafHomFppf_homEquiv_laws F G H).2.1 g)
    ((moduleSheafHomFppf_homEquiv_laws F G H).2.2.1 g _)
  left_inv f := (moduleSheafHomFppf_homEquiv_laws F G H).2.2.2.1 f _ _ _
  right_inv g := (moduleSheafHomFppf_homEquiv_laws F G H).2.2.2.2 g _ _ _

end AlgebraicGeometry.GroupoidsOver
