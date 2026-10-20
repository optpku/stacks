module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import stacks_project.Chap92.«92_25_1_1_Morphism»

/-!
# Naive differentials on `C_{X/Λ}`

This leaf owns the constant sheaf `underline{Λ}` on `C_{X/Λ}`, the structure map
`underline{Λ} ⟶ O`, the sheaf `Ω_{O / underline{Λ}}` of Kähler differentials, and the
pullback `i^* Ω = Ω ⊗_O underline{O}_X`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- The inherited topology on `C_{X/Λ}` admits sheaf composition with
`forget₂ CommRingCat RingCat`. -/
public instance topology_hasSheafCompose_commRing :
    (topology Λ X).HasSheafCompose (forget₂ CommRingCat RingCat.{u}) :=
  sorry

/-- Commutative ring sheaves on `C_{X/Λ}` can be sheafified. -/
public instance topology_hasSheafify_commRing : HasSheafify (topology Λ X) CommRingCat.{u} :=
  sorry

/-- Additive sheafification exists on `C_{X/Λ}`. -/
public instance topology_hasWeakSheafify_addCommGrp :
    HasWeakSheafify (topology Λ X) AddCommGrpCat.{u} :=
  sorry

/-- Additive sheaves on `C_{X/Λ}` can be sheafified. -/
public instance topology_hasSheafify_addCommGrp : HasSheafify (topology Λ X) AddCommGrpCat.{u} :=
  sorry

/-- Locally bijective additive maps on `C_{X/Λ}` are sheaf isomorphisms. -/
public instance topology_wEqualsLocallyBijective_addCommGrp :
    (topology Λ X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- The global-sections presheaf `(U ⟶ A) ↦ Γ(A, O_A)`, valued in commutative rings. -/
def structurePresheafComm : (Obj Λ X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineRealization Λ X).op ⋙ Scheme.Γ

/-- The value of `structurePresheafComm` at `(U ⟶ A)` is `Γ(A, ⊤)`. -/
theorem structurePresheafComm_obj (P : Obj Λ X) :
    (structurePresheafComm Λ X).obj (op P) = Γ(P.A, ⊤) :=
  sorry

/-- The global-sections presheaf `(U ⟶ A) ↦ Γ(A, O_A)` is a sheaf on `C_{X/Λ}`. -/
theorem structurePresheafComm_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (structurePresheafComm Λ X) :=
  sorry

/-- The commutative structure sheaf `O` on `C_{X/Λ}`. -/
def structureSheafComm : Sheaf (topology Λ X) CommRingCat.{u} :=
  ⟨structurePresheafComm Λ X, structurePresheafComm_isSheaf Λ X⟩

/-- The value of `structureSheafComm` at `(U ⟶ A)` is `Γ(A, ⊤)`. -/
theorem structureSheafComm_obj (P : Obj Λ X) :
    (structureSheafComm Λ X).obj.obj (op P) = Γ(P.A, ⊤) :=
  sorry

/-- Forgetting commutativity of `O` recovers `structureSheaf`. -/
theorem structureSheafComm_forget :
    (sheafCompose (topology Λ X) (forget₂ CommRingCat RingCat.{u})).obj
        (structureSheafComm Λ X) =
      structureSheaf Λ X :=
  sorry

/-- The inverse-image presheaf `π⁻¹ O_X`, sending `(U ⟶ A)` to `O_X(U)`, valued in
commutative rings. -/
def inverseImageStructurePresheafComm : (Obj Λ X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (forgetZariski Λ X ⋙ Scheme.smallZariskiToScheme X).op ⋙ Scheme.Γ

/-- The value of `inverseImageStructurePresheafComm` at `(U ⟶ A)` is `Γ(U, ⊤)`. -/
theorem inverseImageStructurePresheafComm_obj (P : Obj Λ X) :
    (inverseImageStructurePresheafComm Λ X).obj (op P) = Γ(P.U.left, ⊤) :=
  sorry

/-- The inverse-image presheaf `π⁻¹ O_X` is a sheaf on `C_{X/Λ}`. -/
theorem inverseImageStructurePresheafComm_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (inverseImageStructurePresheafComm Λ X) :=
  sorry

/-- The commutative sheaf `underline{O}_X = π⁻¹ O_X` on `C_{X/Λ}`. -/
def inverseImageStructureSheafComm : Sheaf (topology Λ X) CommRingCat.{u} :=
  ⟨inverseImageStructurePresheafComm Λ X, inverseImageStructurePresheafComm_isSheaf Λ X⟩

/-- The value of `inverseImageStructureSheafComm` at `(U ⟶ A)` is `Γ(U, ⊤)`. -/
theorem inverseImageStructureSheafComm_obj (P : Obj Λ X) :
    (inverseImageStructureSheafComm Λ X).obj.obj (op P) = Γ(P.U.left, ⊤) :=
  sorry

/-- Forgetting commutativity of `underline{O}_X` recovers `inverseImageStructureSheaf`. -/
theorem inverseImageStructureSheafComm_forget :
    (sheafCompose (topology Λ X) (forget₂ CommRingCat RingCat.{u})).obj
        (inverseImageStructureSheafComm Λ X) =
      inverseImageStructureSheaf Λ X :=
  sorry

/-- The constant sheaf `underline{Λ}` on `C_{X/Λ}`. -/
def constRingSheaf : Sheaf (topology Λ X) CommRingCat.{u} :=
  (constantSheaf (topology Λ X) CommRingCat.{u}).obj Λ

/-- `constRingSheaf` is the constant sheaf with value `Λ`. -/
theorem constRingSheaf_eq :
    constRingSheaf Λ X = (constantSheaf (topology Λ X) CommRingCat.{u}).obj Λ :=
  sorry

/-- The structure morphism `Λ ⟶ Γ(A, O_A)` of an object of `C_{X/Λ}`. -/
def structureMap (P : Obj Λ X) : Λ ⟶ Γ(P.A, ⊤) :=
  homToSpecGlobalSectionsEquiv P.A Λ (specPolynomialToBase Λ P.vars)

/-- Unfolding of `structureMap` through the Gamma-Spec equivalence. -/
theorem structureMap_eq (P : Obj Λ X) :
    structureMap Λ X P = homToSpecGlobalSectionsEquiv P.A Λ (specPolynomialToBase Λ P.vars) :=
  sorry

/-- Component of the constant-to-structure presheaf map at `(U ⟶ A)`. -/
def constToStructurePresheafApp (P : (Obj Λ X)ᵒᵖ) :
    ((Functor.const (Obj Λ X)ᵒᵖ).obj Λ).obj P ⟶ (structureSheafComm Λ X).obj.obj P :=
  structureMap Λ X P.unop

/-- Unfolding of `constToStructurePresheafApp`. -/
theorem constToStructurePresheafApp_eq (P : (Obj Λ X)ᵒᵖ) :
    constToStructurePresheafApp Λ X P = structureMap Λ X P.unop :=
  sorry

/-- The constant-to-structure map of presheaves, before sheafification. -/
def constToStructurePresheaf :
    (Functor.const (Obj Λ X)ᵒᵖ).obj Λ ⟶ (structureSheafComm Λ X).obj where
  app P := constToStructurePresheafApp Λ X P
  naturality := fun _ _ _ ↦ sorry

/-- Unfolding of `constToStructurePresheaf` at an object of `C_{X/Λ}`. -/
theorem constToStructurePresheaf_app (P : (Obj Λ X)ᵒᵖ) :
    (constToStructurePresheaf Λ X).app P = constToStructurePresheafApp Λ X P :=
  sorry

/-- The canonical algebra map `underline{Λ} ⟶ O` on `C_{X/Λ}`. -/
def constToStructure : constRingSheaf Λ X ⟶ structureSheafComm Λ X :=
  ((sheafificationAdjunction (topology Λ X) CommRingCat.{u}).homEquiv
      ((Functor.const (Obj Λ X)ᵒᵖ).obj Λ) (structureSheafComm Λ X)).symm
    (constToStructurePresheaf Λ X)

/-- `constToStructure` is the sheafification adjunct of `constToStructurePresheaf`. -/
theorem constToStructure_eq :
    constToStructure Λ X =
      ((sheafificationAdjunction (topology Λ X) CommRingCat.{u}).homEquiv
          ((Functor.const (Obj Λ X)ᵒᵖ).obj Λ) (structureSheafComm Λ X)).symm
        (constToStructurePresheaf Λ X) :=
  sorry

/-- The component of `constToStructure` at `(U ⟶ A)` after the sheafification unit is
`structureMap`. -/
theorem constToStructure_app (P : (Obj Λ X)ᵒᵖ) :
    ((sheafificationAdjunction (topology Λ X) CommRingCat.{u}).unit.app
          ((Functor.const (Obj Λ X)ᵒᵖ).obj Λ)).app P ≫
        (constToStructure Λ X).hom.app P =
      structureMap Λ X P.unop :=
  sorry

/-- The obvious sheaf map `i♯ : O ⟶ underline{O}_X`, as a map of commutative ring sheaves. -/
def structureSheafMapComm : structureSheafComm Λ X ⟶ inverseImageStructureSheafComm Λ X where
  hom :=
    { app P := P.unop.hom.appTop
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `structureSheafMapComm` at `(U ⟶ A)` is `A ⟶ U` on global sections. -/
theorem structureSheafMapComm_app (P : Obj Λ X) :
    (structureSheafMapComm Λ X).hom.app (op P) = P.hom.appTop :=
  sorry

/-- Forgetting commutativity of `structureSheafMapComm` recovers `structureSheafMap`. -/
theorem structureSheafMapComm_forget :
    (sheafCompose (topology Λ X) (forget₂ CommRingCat RingCat.{u})).map
        (structureSheafMapComm Λ X) =
      structureSheafMap Λ X :=
  sorry

/-- Naive differentials of an object `(U ⟶ A)` of `C_{X/Λ}`, as the `Γ(A)`-module
`Ω[Γ(A) ⁄ Λ]`. -/
def omegaSheafObj (P : Obj Λ X) : ModuleCat.{u} Γ(P.A, ⊤) :=
  CommRingCat.KaehlerDifferential (structureMap Λ X P)

/-- Unfolding of `omegaSheafObj` as Kähler differentials of `structureMap`. -/
theorem omegaSheafObj_eq (P : Obj Λ X) :
    omegaSheafObj Λ X P = CommRingCat.KaehlerDifferential (structureMap Λ X P) :=
  sorry

/-- The presheaf of naive differentials `Ω_{O / underline{Λ}}` on `C_{X/Λ}`. -/
def omegaSheafVal :
    PresheafOfModules.{u}
      ((structureSheafComm Λ X).obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
  relativeDifferentials' (constToStructurePresheaf Λ X)

/-- Evaluating `omegaSheafVal` at `(U ⟶ A)` recovers `omegaSheafObj`. -/
theorem omegaSheafVal_obj (P : Obj Λ X) :
    (omegaSheafVal Λ X).obj (op P) = omegaSheafObj Λ X P :=
  sorry

/-- The sheaf of naive differentials `Ω_{O / underline{Λ}}` on `C_{X/Λ}`. -/
def omegaSheaf : SheafOfModules.{u} (structureSheaf Λ X) where
  val := omegaSheafVal Λ X
  isSheaf := sorry

/-- Evaluating `omegaSheaf` at `(U ⟶ A)` recovers `omegaSheafObj`. -/
theorem omegaSheaf_obj (P : Obj Λ X) :
    (omegaSheaf Λ X).val.obj (op P) = omegaSheafObj Λ X P :=
  sorry

/-- The sheaf `omegaSheaf` is the objectwise Kähler presheaf `omegaSheafVal`. -/
theorem omegaSheaf_val :
    (omegaSheaf Λ X).val = omegaSheafVal Λ X :=
  sorry

/-- Naive pullback differentials of an object `(U ⟶ A)`, as the `O_X(U)`-module
`Ω[Γ(A) ⁄ Λ] ⊗[Γ(A)] O_X(U)`. -/
def omegaPullbackObj (P : Obj Λ X) : ModuleCat.{u} Γ(P.U.left, ⊤) :=
  (ModuleCat.extendScalars P.hom.appTop.hom).obj (omegaSheafObj Λ X P)

/-- Unfolding of `omegaPullbackObj` as extension of scalars of `omegaSheafObj`. -/
theorem omegaPullbackObj_eq (P : Obj Λ X) :
    omegaPullbackObj Λ X P =
      (ModuleCat.extendScalars P.hom.appTop.hom).obj (omegaSheafObj Λ X P) :=
  sorry

/-- The structure maps `Γ(A) ⟶ O_X(U)` are natural in morphisms of `C_{X/Λ}`. -/
theorem structureSheafMapComm_naturality {P Q : (Obj Λ X)ᵒᵖ} (f : P ⟶ Q) :
    P.unop.hom.appTop ≫ (inverseImageStructureSheafComm Λ X).obj.map f =
      (structureSheafComm Λ X).obj.map f ≫ Q.unop.hom.appTop :=
  sorry

/-- The two composite ring maps `Γ(A) ⟶ O_X(V)` attached to a morphism of `C_{X/Λ}`
agree. -/
theorem omegaPullbackMap_comp_eq {P Q : (Obj Λ X)ᵒᵖ} (f : P ⟶ Q) :
    Q.unop.hom.appTop.hom.comp ((structureSheafComm Λ X).obj.map f).hom =
      ((inverseImageStructureSheafComm Λ X).obj.map f).hom.comp
        P.unop.hom.appTop.hom :=
  sorry

/-- Restriction maps of `omegaPullback` along a morphism of `C_{X/Λ}`. -/
def omegaPullbackMap {P Q : (Obj Λ X)ᵒᵖ} (f : P ⟶ Q) :
    omegaPullbackObj Λ X P.unop ⟶
      (ModuleCat.restrictScalars
        ((inverseImageStructureSheafComm Λ X).obj.map f).hom).obj
        (omegaPullbackObj Λ X Q.unop) :=
  ((ModuleCat.extendRestrictScalarsAdj P.unop.hom.appTop.hom).homEquiv _ _).symm
    ((omegaSheafVal Λ X).map f ≫
      (ModuleCat.restrictScalars ((structureSheafComm Λ X).obj.map f).hom).map
        ((ModuleCat.extendRestrictScalarsAdj Q.unop.hom.appTop.hom).unit.app
          ((omegaSheafVal Λ X).obj Q)) ≫
      (ModuleCat.restrictScalarsComp'
          ((structureSheafComm Λ X).obj.map f).hom Q.unop.hom.appTop.hom
          (Q.unop.hom.appTop.hom.comp ((structureSheafComm Λ X).obj.map f).hom) rfl).inv.app _ ≫
      (ModuleCat.restrictScalarsCongr (omegaPullbackMap_comp_eq Λ X f)).hom.app _ ≫
      (ModuleCat.restrictScalarsComp'
          P.unop.hom.appTop.hom ((inverseImageStructureSheafComm Λ X).obj.map f).hom
          (((inverseImageStructureSheafComm Λ X).obj.map f).hom.comp P.unop.hom.appTop.hom)
          rfl).hom.app _)

/-- Unfolding of `omegaPullbackMap` as the adjunct of the Kähler restriction. -/
theorem omegaPullbackMap_eq {P Q : (Obj Λ X)ᵒᵖ} (f : P ⟶ Q) :
    omegaPullbackMap Λ X f =
      ((ModuleCat.extendRestrictScalarsAdj P.unop.hom.appTop.hom).homEquiv _ _).symm
        ((omegaSheafVal Λ X).map f ≫
          (ModuleCat.restrictScalars ((structureSheafComm Λ X).obj.map f).hom).map
            ((ModuleCat.extendRestrictScalarsAdj Q.unop.hom.appTop.hom).unit.app
              ((omegaSheafVal Λ X).obj Q)) ≫
          (ModuleCat.restrictScalarsComp'
              ((structureSheafComm Λ X).obj.map f).hom Q.unop.hom.appTop.hom
              (Q.unop.hom.appTop.hom.comp ((structureSheafComm Λ X).obj.map f).hom)
              rfl).inv.app _ ≫
          (ModuleCat.restrictScalarsCongr (omegaPullbackMap_comp_eq Λ X f)).hom.app _ ≫
          (ModuleCat.restrictScalarsComp'
              P.unop.hom.appTop.hom ((inverseImageStructureSheafComm Λ X).obj.map f).hom
              (((inverseImageStructureSheafComm Λ X).obj.map f).hom.comp
                P.unop.hom.appTop.hom) rfl).hom.app _) :=
  sorry

/-- The presheaf of pullback differentials `i^* Ω_{O / underline{Λ}}` on `C_{X/Λ}`. -/
def omegaPullbackVal :
    PresheafOfModules.{u}
      ((inverseImageStructureSheafComm Λ X).obj ⋙ forget₂ CommRingCat RingCat.{u}) where
  obj P := omegaPullbackObj Λ X P.unop
  map f := omegaPullbackMap Λ X f
  map_id := sorry
  map_comp := sorry

/-- Evaluating `omegaPullbackVal` at `(U ⟶ A)` recovers `omegaPullbackObj`. -/
theorem omegaPullbackVal_obj (P : Obj Λ X) :
    (omegaPullbackVal Λ X).obj (op P) = omegaPullbackObj Λ X P :=
  sorry

/-- The sheaf `i^* Ω_{O / underline{Λ}} = Ω_{O / underline{Λ}} ⊗_O underline{O}_X`. -/
def omegaPullback : SheafOfModules.{u} (inverseImageStructureSheaf Λ X) where
  val := omegaPullbackVal Λ X
  isSheaf := sorry

/-- Evaluating `omegaPullback` at `(U ⟶ A)` recovers `omegaPullbackObj`. -/
theorem omegaPullback_obj (P : Obj Λ X) :
    (omegaPullback Λ X).val.obj (op P) = omegaPullbackObj Λ X P :=
  sorry

/-- Restriction of scalars along `i♯` is a right adjoint. -/
public instance structureSheafMap_restrictScalars_isRightAdjoint :
    (SheafOfModules.restrictScalars (structureSheafMap Λ X)).IsRightAdjoint :=
  sorry

/-- Sheaf-level extension of scalars along `i♯` applied to `omegaSheaf`. -/
def omegaPullbackExtend : SheafOfModules.{u} (inverseImageStructureSheaf Λ X) :=
  (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X)).obj (omegaSheaf Λ X)

/-- Unfolding of `omegaPullbackExtend` as sheaf-level extension of scalars. -/
theorem omegaPullbackExtend_eq :
    omegaPullbackExtend Λ X =
      (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X)).obj
        (omegaSheaf Λ X) :=
  sorry

/-- The adjunction unit `Ω ⟶ i_* i^* Ω` on `C_{X/Λ}`, objectwise the extension-of-scalars
unit of `Γ(A) ⟶ O_X(U)`. -/
def omegaSheafToRestrictPullback :
    omegaSheaf Λ X ⟶
      (SheafOfModules.restrictScalars (structureSheafMap Λ X)).obj (omegaPullback Λ X) where
  val :=
    { app P :=
        (ModuleCat.extendRestrictScalarsAdj P.unop.hom.appTop.hom).unit.app
          ((omegaSheaf Λ X).val.obj P)
      naturality := fun {_ _} _ ↦ sorry }

/-- Unfolding of `omegaSheafToRestrictPullback` at `(U ⟶ A)`. -/
theorem omegaSheafToRestrictPullback_app (P : Obj Λ X) :
    (omegaSheafToRestrictPullback Λ X).val.app (op P) =
      (ModuleCat.extendRestrictScalarsAdj P.hom.appTop.hom).unit.app
        ((omegaSheaf Λ X).val.obj (op P)) :=
  sorry

/-- The canonical sheaf morphism from sheaf-level extension of scalars along `i♯` to the
objectwise tensor presentation of `i^* Ω`. -/
def omegaExtendToPullback :
    omegaPullbackExtend Λ X ⟶ omegaPullback Λ X :=
  (SheafOfModules.ChangeOfRings.extendRestrictHomEquiv (structureSheafMap Λ X)
      (omegaSheaf Λ X) (omegaPullback Λ X)).symm
    (omegaSheafToRestrictPullback Λ X)

/-- `omegaExtendToPullback` is the adjunct of `omegaSheafToRestrictPullback`. -/
theorem omegaExtendToPullback_eq :
    omegaExtendToPullback Λ X =
      (SheafOfModules.ChangeOfRings.extendRestrictHomEquiv (structureSheafMap Λ X)
          (omegaSheaf Λ X) (omegaPullback Λ X)).symm
        (omegaSheafToRestrictPullback Λ X) :=
  sorry

/-- Objectwise tensor and sheaf-level extension of scalars present the same `i^* Ω`. -/
instance omegaExtendToPullback_isIso : IsIso (omegaExtendToPullback Λ X) :=
  sorry

/-- Objectwise tensor presentation of `i^* Ω` is canonically isomorphic to sheaf-level
extension of scalars along `i♯`. -/
def omegaPullbackIsoExtend : omegaPullback Λ X ≅ omegaPullbackExtend Λ X :=
  (asIso (omegaExtendToPullback Λ X)).symm

/-- The inverse of `omegaPullbackIsoExtend` is `omegaExtendToPullback`. -/
theorem omegaPullbackIsoExtend_inv :
    (omegaPullbackIsoExtend Λ X).inv = omegaExtendToPullback Λ X :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
