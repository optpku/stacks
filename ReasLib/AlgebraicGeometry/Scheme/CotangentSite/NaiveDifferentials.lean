/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec

/-!
# Differentials of polynomial affine diagrams

Raw Kähler and tensor presheaves retain their sectionwise formulas in the
original coefficient universe. Differential sheaves use the associated ring
sheaves in the successor universe, and tensor pullback is sheaf-level extension
of scalars. Sheafification comparisons are global, rather than equalities of
raw values at individual diagrams.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- The constant associated sheaf of the lifted base ring. -/
def constRingSheaf : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (constantSheaf (topology Λ X) CommRingCat.{u + 1}).obj
    ((CommRingCat.universeLift.{u, u + 1}).obj Λ)

/-- The base-ring map to global functions on the actual affine target. -/
def structureMap (P : category Λ X) : Λ ⟶ Γ(P.right.obj.left, ⊤) :=
  homToSpecGlobalSectionsEquiv P.right.obj.left Λ P.right.obj.hom

/-- The raw constant-to-functions component at an affine diagram. -/
def constToStructurePresheafApp (P : (category Λ X)ᵒᵖ) :
    ((Functor.const (category Λ X)ᵒᵖ).obj Λ).obj P ⟶
      (structurePresheafComm Λ X).obj P :=
  structureMap Λ X P.unop

/-- The base morphisms induce a natural transformation of raw function presheaves. -/
def constToStructurePresheaf :
    (Functor.const (category Λ X)ᵒᵖ).obj Λ ⟶ structurePresheafComm Λ X where
  app P := constToStructurePresheafApp Λ X P
  naturality := fun _ _ _ ↦ sorry

/-- The raw constant-to-functions map has the specified base-ring component. -/
theorem constToStructurePresheaf_app (P : (category Λ X)ᵒᵖ) :
    (constToStructurePresheaf Λ X).app P = constToStructurePresheafApp Λ X P := rfl

/-- The universe lift of the raw constant-to-functions map. -/
def constToStructurePresheafLift :
    (Functor.const (category Λ X)ᵒᵖ).obj
        ((CommRingCat.universeLift.{u, u + 1}).obj Λ) ⟶
      structurePresheafCommLift Λ X :=
  Functor.whiskerRight (constToStructurePresheaf Λ X) CommRingCat.universeLift

/-- The morphism from the constant associated sheaf to the associated structure sheaf,
obtained by adjunction after the target sheafification unit. -/
def constToStructure : constRingSheaf Λ X ⟶ structureSheafComm Λ X :=
  ((sheafificationAdjunction (topology Λ X) CommRingCat.{u + 1}).homEquiv
      _ (structureSheafComm Λ X)).symm
    (constToStructurePresheafLift Λ X ≫ structureSheafUnit Λ X)

/-- The constant-sheaf structure map is compatible with both sheafification units. -/
theorem constToStructure_app (P : (category Λ X)ᵒᵖ) :
    (toSheafify (topology Λ X)
        ((Functor.const (category Λ X)ᵒᵖ).obj
          ((CommRingCat.universeLift.{u, u + 1}).obj Λ))).app P ≫
        (constToStructure Λ X).hom.app P =
      (constToStructurePresheafLift Λ X).app P ≫ (structureSheafUnit Λ X).app P := sorry

/-- The raw module of Kähler differentials of the target algebra. -/
def omegaSheafObj (P : category Λ X) : ModuleCat.{u} Γ(P.right.obj.left, ⊤) :=
  CommRingCat.KaehlerDifferential (structureMap Λ X P)

/-- The raw presheaf of differentials of target global functions. -/
def omegaSheafVal :
    _root_.PresheafOfModules.{u} (structurePresheafComm Λ X ⋙ forget₂ CommRingCat RingCat.{u}) :=
  relativeDifferentials' (constToStructurePresheaf Λ X)

/-- The raw differential presheaf evaluates to target Kähler differentials. -/
theorem omegaSheafVal_obj (P : category Λ X) :
    (omegaSheafVal Λ X).obj (op P) = omegaSheafObj Λ X P := rfl

/-- The sheaf of differentials of the associated structure sheaf over the constant sheaf. -/
def omegaSheaf : SheafOfModules.{u + 1} (structureSheaf Λ X) :=
  relativeDifferentials.{u + 1, u, u + 1} (J := topology Λ X) (constToStructure Λ X)

/-- Differential sheafification identifies lifted raw Kähler differentials with
relative differentials of the associated ring sheaves. -/
theorem omegaSheaf_sheafification :
    IsIsomorphic (omegaSheaf Λ X)
      ((PresheafOfModules.moduleSheafification.{u + 1, u, u + 1, u + 1} (topology Λ X)
          (structurePresheafCommLift Λ X)).obj
        (relativeDifferentials' (constToStructurePresheafLift Λ X))) := sorry

/-- The differential sheaf of polynomial affine targets is flat over the associated
structure sheaf. -/
instance omegaSheaf_isFlat :
    SheafOfModules.RingedSite.IsFlat (J := topology Λ X) (structureSheafComm Λ X) (omegaSheaf Λ X) := sorry

/-- Raw pullback differentials are extension of scalars from target functions
to open-vertex functions. -/
def omegaPullbackObj (P : category Λ X) : ModuleCat.{u} Γ(P.left.left, ⊤) :=
  (ModuleCat.extendScalars P.hom.left.appTop.hom).obj (omegaSheafObj Λ X P)

/-- The two composite ring maps `Γ(A) ⟶ O_X(V)` attached to a morphism of `C_{X/Λ}`
agree. -/
theorem omegaPullbackMap_comp_eq {P Q : (category Λ X)ᵒᵖ} (f : P ⟶ Q) :
    Q.unop.hom.left.appTop.hom.comp ((structurePresheafComm Λ X).map f).hom =
      ((inverseImageStructurePresheafComm Λ X).map f).hom.comp
        P.unop.hom.left.appTop.hom :=
  sorry

/-- Restriction of raw tensor differentials along a morphism of polynomial affine diagrams. -/
def omegaPullbackMap {P Q : (category Λ X)ᵒᵖ} (f : P ⟶ Q) :
    omegaPullbackObj Λ X P.unop ⟶
      (ModuleCat.restrictScalars
        ((inverseImageStructurePresheafComm Λ X).map f).hom).obj
        (omegaPullbackObj Λ X Q.unop) :=
  ((ModuleCat.extendRestrictScalarsAdj P.unop.hom.left.appTop.hom).homEquiv _ _).symm
    ((omegaSheafVal Λ X).map f ≫
      (ModuleCat.restrictScalars ((structurePresheafComm Λ X).map f).hom).map
        ((ModuleCat.extendRestrictScalarsAdj Q.unop.hom.left.appTop.hom).unit.app
          ((omegaSheafVal Λ X).obj Q)) ≫
      (ModuleCat.restrictScalarsComp'
          ((structurePresheafComm Λ X).map f).hom Q.unop.hom.left.appTop.hom
          (Q.unop.hom.left.appTop.hom.comp ((structurePresheafComm Λ X).map f).hom) rfl).inv.app _ ≫
      (ModuleCat.restrictScalarsCongr (omegaPullbackMap_comp_eq Λ X f)).hom.app _ ≫
      (ModuleCat.restrictScalarsComp'
          P.unop.hom.left.appTop.hom ((inverseImageStructurePresheafComm Λ X).map f).hom
          (((inverseImageStructurePresheafComm Λ X).map f).hom.comp P.unop.hom.left.appTop.hom)
          rfl).hom.app _)

/-- The raw tensor presheaf, with functoriality given by tensor restriction maps. -/
def omegaPullbackVal :
    _root_.PresheafOfModules.{u}
      (inverseImageStructurePresheafComm Λ X ⋙ forget₂ CommRingCat RingCat.{u}) := by
  refine { obj := fun P ↦ omegaPullbackObj Λ X P.unop
           map := fun f ↦ omegaPullbackMap Λ X f
           map_id := ?_
           map_comp := ?_ }
  all_goals sorry

/-- The raw tensor presheaf evaluates to extension of the target differential module. -/
theorem omegaPullbackVal_obj (P : category Λ X) :
    (omegaPullbackVal Λ X).obj (op P) = omegaPullbackObj Λ X P := rfl

/-- Pullback of differential sheaves is genuine sheaf-level extension of scalars. -/
def omegaPullback : SheafOfModules.{u + 1} (inverseImageStructureSheaf Λ X) :=
  (SheafOfModules.RingedSite.extendAlong (J := topology Λ X) (structureSheafMapComm Λ X)).obj (omegaSheaf Λ X)

/-- Sheafification of the lifted raw tensor presheaf agrees with extension of scalars
on the associated differential sheaf. -/
theorem omegaPullback_sheafification :
    IsIsomorphic (omegaPullback Λ X)
      ((PresheafOfModules.moduleSheafification.{u + 1, u, u + 1, u + 1} (topology Λ X)
          (inverseImageStructurePresheafCommLift Λ X)).obj
        ((PresheafOfModules.SameSiteTensorExtension.functor
            (structurePresheafMapLift Λ X)).obj
          (relativeDifferentials' (constToStructurePresheafLift Λ X)))) := sorry

/-- The canonical map from differentials to the restriction of their scalar extension
is the extension-restriction adjunction unit. -/
def omegaSheafToRestrictPullback :
    omegaSheaf Λ X ⟶
      (SheafOfModules.RingedSite.restrictionAlong (J := topology Λ X)
        (structureSheafMapComm Λ X)).obj (omegaPullback Λ X) :=
  (SheafOfModules.RingedSite.extendRestrictAdj (J := topology Λ X)
    (structureSheafMapComm Λ X)).unit.app (omegaSheaf Λ X)

/-- The differential-to-pullback map is the whole-map adjunction unit. -/
theorem omegaSheafToRestrictPullback_eq :
    omegaSheafToRestrictPullback Λ X =
      (SheafOfModules.RingedSite.extendRestrictAdj (J := topology Λ X)
        (structureSheafMapComm Λ X)).unit.app (omegaSheaf Λ X) := rfl

end AlgebraicGeometry.Scheme.CotangentSite
