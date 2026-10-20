/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.Wedge
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/-- A scheme morphism commutes with the structure morphisms to the terminal scheme. -/
theorem absoluteSquare {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CommSq f (terminal.from Y) (terminal.from X) (𝟙 _) := by
  constructor
  simp

-- The scoped visibility option exports private implementation dependencies needed by the
-- exposed comparison, while keeping these one-use names out of the public mathematical API.
set_option backward.privateInPublic true in
private theorem presentedDifferential_laws {A B : CommRingCat.{u}} (g : A ⟶ B) :
    (∀ x y : B, CommRingCat.DeRham.basic g 1 1 (fun _ ↦ x + y) =
      CommRingCat.DeRham.basic g 1 1 (fun _ ↦ x) +
        CommRingCat.DeRham.basic g 1 1 (fun _ ↦ y)) ∧
    (∀ x y : B, CommRingCat.DeRham.basic g 1 1 (fun _ ↦ x * y) =
      x • CommRingCat.DeRham.basic g 1 1 (fun _ ↦ y) +
        y • CommRingCat.DeRham.basic g 1 1 (fun _ ↦ x)) ∧
    (∀ a : A, CommRingCat.DeRham.basic g 1 1 (fun _ ↦ g a) = 0) := sorry

set_option backward.privateInPublic true in
private def presentedDifferential {A B : CommRingCat.{u}} (g : A ⟶ B) :
    (CommRingCat.DeRham.form g 1).Derivation g :=
  ModuleCat.Derivation.mk
    (fun b ↦ CommRingCat.DeRham.basic g 1 1 (fun _ ↦ b))
    (presentedDifferential_laws g).1
    (presentedDifferential_laws g).2.1
    (presentedDifferential_laws g).2.2

set_option backward.privateInPublic true in
private def algebraicDifferentialToPresented {A B : CommRingCat.{u}} (g : A ⟶ B) :
    CommRingCat.KaehlerDifferential g ⟶ CommRingCat.DeRham.form g 1 :=
  (presentedDifferential g).desc

set_option backward.privateInPublic true in
private theorem oneFormToPresentedPresheaf_naturality {S X : Scheme.{u}} (g : X ⟶ S)
    {U V : X.Opensᵒᵖ} (a : U ⟶ V) :
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
        (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom).map a ≫
      (ModuleCat.restrictScalars (X.𝒪.obj.map a).hom).map
        (algebraicDifferentialToPresented
          ((RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom.app V)) =
    algebraicDifferentialToPresented
        ((RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom.app U) ≫
      (PresheafOfModules.DeRham.form
        (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom 1).map a := sorry

set_option backward.privateInPublic true in
private def oneFormToPresentedPresheaf {S X : Scheme.{u}} (g : X ⟶ S) :
    PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
        (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom ⟶
      PresheafOfModules.DeRham.form
        (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom 1 where
  app U := algebraicDifferentialToPresented
    ((RingedSpace.DeRham.structureMap g.toLRSHom.toShHom).hom.app U)
  naturality a := oneFormToPresentedPresheaf_naturality g a

set_option backward.privateInPublic true in
private def oneFormToPresented {S X : Scheme.{u}} (g : X ⟶ S) :
    Ω[g.toShHom] ⟶ RingedSpace.DeRham.form g.toLRSHom.toShHom 1 :=
  (moduleSheafification X.𝒪).map (oneFormToPresentedPresheaf g)

set_option backward.privateInPublic true in
private theorem presentedUnit_naturality {S X : Scheme.{u}} (g : X ⟶ S)
    {U V : X.Opensᵒᵖ} (a : U ⟶ V) (b : X.𝒪.obj.obj U) :
    (RingedSpace.DeRham.form g.toLRSHom.toShHom 0).val.map a
        (b • DeRham.basicForm (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom)
          0 U 1 (fun i ↦ Fin.elim0 i)) =
      (X.𝒪.obj.map a b) •
        DeRham.basicForm (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom)
          0 V 1 (fun i ↦ Fin.elim0 i) := sorry

set_option backward.privateInPublic true in
private def presentedUnit {S X : Scheme.{u}} (g : X ⟶ S) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      RingedSpace.DeRham.form g.toLRSHom.toShHom 0 where
  val :=
    { app U := ModuleCat.ofHom (R := X.𝒪.obj.obj U)
        (X := X.𝒪.obj.obj U)
        (Y := (RingedSpace.DeRham.form g.toLRSHom.toShHom 0).val.obj U)
        (LinearMap.toSpanSingleton (X.𝒪.obj.obj U)
          ((RingedSpace.DeRham.form g.toLRSHom.toShHom 0).val.obj U)
          (DeRham.basicForm (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom)
            0 U 1 (fun i ↦ Fin.elim0 i)))
      naturality a := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        exact (presentedUnit_naturality g a b).symm }

set_option backward.privateInPublic true in
private def presentedWedgeApp {S X : Scheme.{u}} (g : X ⟶ S) (p q : ℕ)
    (U : X.Opensᵒᵖ)
    (x : (RingedSpace.DeRham.form g.toLRSHom.toShHom p).val.obj U)
    (y : (RingedSpace.DeRham.form g.toLRSHom.toShHom q).val.obj U) :
    (RingedSpace.DeRham.form g.toLRSHom.toShHom (p + q)).val.obj U :=
  ((moduleSheafificationUnitToVal X.𝒪
        ((RingedSpace.DeRham.form g.toLRSHom.toShHom p).val ⊗
          (RingedSpace.DeRham.form g.toLRSHom.toShHom q).val) ≫
      (ModuleSheafification.tensorObjIso X.𝒪
        (RingedSpace.DeRham.form g.toLRSHom.toShHom p)
        (RingedSpace.DeRham.form g.toLRSHom.toShHom q)).inv.val ≫
      (DeRham.formWedge (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom) p q).val).app U)
    (x ⊗ₜ[X.𝒪.obj.obj U] y)

set_option backward.privateInPublic true in
private def presentedProductApp {S X : Scheme.{u}} (g : X ⟶ S) (U : X.Opensᵒᵖ) :
    (p : ℕ) → (Fin p → Ω[g.toShHom].val.obj U) →
      (RingedSpace.DeRham.form g.toLRSHom.toShHom p).val.obj U
  | 0, _ => (presentedUnit g).val.app U (1 : X.𝒪.obj.obj U)
  | n + 1, v =>
      (eqToHom (congrArg
        (fun k ↦ (RingedSpace.DeRham.form g.toLRSHom.toShHom k).val.obj U)
        (Nat.add_comm 1 n)))
        (presentedWedgeApp g 1 n U
          ((oneFormToPresented g).val.app U (v 0))
          (presentedProductApp g U n (fun i ↦ v i.succ)))

set_option backward.privateInPublic true in
private theorem presentedProductApp_laws {S X : Scheme.{u}} (g : X ⟶ S)
    (U : X.Opensᵒᵖ) (p : ℕ) :
    (∀ [DecidableEq (Fin p)] (v : Fin p → Ω[g.toShHom].val.obj U)
      (i : Fin p) (x y : Ω[g.toShHom].val.obj U),
      presentedProductApp g U p (Function.update v i (x + y)) =
        presentedProductApp g U p (Function.update v i x) +
          presentedProductApp g U p (Function.update v i y)) ∧
    (∀ [DecidableEq (Fin p)] (v : Fin p → Ω[g.toShHom].val.obj U)
      (i : Fin p) (c : X.𝒪.obj.obj U) (x : Ω[g.toShHom].val.obj U),
      presentedProductApp g U p (Function.update v i (c • x)) =
        c • presentedProductApp g U p (Function.update v i x)) ∧
    (∀ (v : Fin p → Ω[g.toShHom].val.obj U) (i j : Fin p),
      v i = v j → i ≠ j → presentedProductApp g U p v = 0) := sorry

set_option backward.privateInPublic true in
private theorem exteriorToFormPresheaf_naturality {S X : Scheme.{u}} (g : X ⟶ S)
    (p : ℕ) {U V : X.Opensᵒᵖ} (a : U ⟶ V) :
    let lift := fun W : X.Opensᵒᵖ ↦ ModuleCat.exteriorPower.desc
      (R := X.𝒪.obj.obj W)
      (M := Ω[g.toShHom].val.obj W)
      (N := (RingedSpace.DeRham.form g.toLRSHom.toShHom p).val.obj W)
      { toFun := presentedProductApp g W p
        map_update_add' := (presentedProductApp_laws g W p).1
        map_update_smul' := (presentedProductApp_laws g W p).2.1
        map_eq_zero_of_eq' := (presentedProductApp_laws g W p).2.2 }
    (PresheafOfModules.ExteriorPower.presheaf X.𝒪.obj Ω[g.toShHom].val p).map a ≫
        (ModuleCat.restrictScalars (X.𝒪.obj.map a).hom).map (lift V) =
      lift U ≫ (RingedSpace.DeRham.form g.toLRSHom.toShHom p).val.map a := sorry

set_option backward.privateInPublic true in
private def exteriorToFormPresheaf {S X : Scheme.{u}} (g : X ⟶ S) (p : ℕ) :
    PresheafOfModules.ExteriorPower.presheaf X.𝒪.obj Ω[g.toShHom].val p ⟶
      (RingedSpace.DeRham.form g.toLRSHom.toShHom p).val where
  app U := ModuleCat.exteriorPower.desc (R := X.𝒪.obj.obj U)
    { toFun := presentedProductApp g U p
      map_update_add' := (presentedProductApp_laws g U p).1
      map_update_smul' := (presentedProductApp_laws g U p).2.1
      map_eq_zero_of_eq' := (presentedProductApp_laws g U p).2.2 }
  naturality a := exteriorToFormPresheaf_naturality g p a

-- Export the private implementation for the exposed comparison while keeping its names private.
set_option backward.privateInPublic true in
/-- Exterior powers of relative differentials map to presented forms by alternating wedge
multiplication of their degree-one images. -/
def exteriorToForm {S X : Scheme.{u}} (g : X ⟶ S) (p : ℕ) :
    (Λ[p] Ω[g.toShHom]) ⟶ RingedSpace.DeRham.form g.toLRSHom.toShHom p :=
  (moduleSheafificationHomEquiv X.𝒪 _ _).symm (exteriorToFormPresheaf g p)

/-- A wedge of universal differentials maps to the corresponding presented basic form. -/
theorem exteriorToForm_ιMulti {S X : Scheme.{u}} (g : X ⟶ S) (p : ℕ)
    (U : X.Opensᵒᵖ) (b : Fin p → X.𝒪.obj.obj U) :
    (exteriorToForm g p).val.app U
        ((moduleSheafificationUnitToVal X.𝒪
          (PresheafOfModules.ExteriorPower.presheaf X.𝒪.obj Ω[g.toShHom].val p)).app U
            (ModuleCat.exteriorPower.mk (R := X.𝒪.obj.obj U)
              (M := Ω[g.toShHom].val.obj U) (fun i ↦
              (RingedSpace.Hom.universalDerivation g.toLRSHom.toShHom).d (b i)))) =
      DeRham.basicForm (RingedSpace.DeRham.structureMap g.toLRSHom.toShHom)
        p U 1 b := sorry

/-- The forward comparison followed by the alternating wedge comparison fixes presented forms. -/
theorem formToExterior_exteriorToForm {S X : Scheme.{u}} (g : X ⟶ S) (p : ℕ) :
    Scheme.DeRham.Gysin.formToExterior g p ≫ exteriorToForm g p = 𝟙 _ := sorry

/-- The alternating wedge comparison followed by the forward comparison fixes exterior forms. -/
theorem exteriorToForm_formToExterior {S X : Scheme.{u}} (g : X ⟶ S) (p : ℕ) :
    exteriorToForm g p ≫ Scheme.DeRham.Gysin.formToExterior g p = 𝟙 _ := sorry

/-- Presented relative forms are canonically isomorphic to exterior powers of relative
differentials. -/
def formExteriorIso {S X : Scheme.{u}} (g : X ⟶ S) (p : ℕ) :
    RingedSpace.DeRham.form g.toLRSHom.toShHom p ≅ Λ[p] Ω[g.toShHom] where
  hom := Scheme.DeRham.Gysin.formToExterior g p
  inv := exteriorToForm g p
  hom_inv_id := formToExterior_exteriorToForm g p
  inv_hom_id := exteriorToForm_formToExterior g p

/-- The canonical square comparing absolute and relative forms for a scheme over a base. -/
theorem absoluteToRelativeSquare {S X : Scheme.{u}} (g : X ⟶ S) :
    CommSq (𝟙 X) g (terminal.from X) (terminal.from S) := by
  constructor
  simp

/-- The canonical quotient map from absolute exterior-power forms to relative forms over `S`. -/
noncomputable def absoluteToRelativeForm {S X : Scheme.{u}}
    (g : X ⟶ S) (p : ℕ) :
    (Λ[p] Ω[(terminal.from X).toShHom]) ⟶ (Λ[p] Ω[g.toShHom]) :=
  (Scheme.Modules.pullbackId X).inv.app
      (Λ[p] Ω[(terminal.from X).toShHom]) ≫
    formComparison (absoluteToRelativeSquare g) p

/-- The absolute-to-relative form map is the identity-pullback comparison followed by the
relative-form comparison. -/
theorem absoluteToRelativeForm_def {S X : Scheme.{u}}
    (g : X ⟶ S) (p : ℕ) :
    absoluteToRelativeForm g p =
      (Scheme.Modules.pullbackId X).inv.app
          (Λ[p] Ω[(terminal.from X).toShHom]) ≫
        formComparison (absoluteToRelativeSquare g) p := rfl

/-- The canonical absolute-to-relative comparison on de Rham terms after forgetting their
coefficient-module structures. -/
noncomputable def absoluteToRelativeTerm {S X : Scheme.{u}}
    (g : X ⟶ S) (p : ℕ) :
    (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients
            (terminal.from X).toLRSHom.toShHom))).obj
        ((RingedSpace.DeRham.complex
          (terminal.from X).toLRSHom.toShHom).X p) ⟶
      (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients g.toLRSHom.toShHom))).obj
        ((RingedSpace.DeRham.complex g.toLRSHom.toShHom).X p) :=
  (SheafOfModules.toSheaf
    (TopCat.Sheaf.ringSheafOfComm
      (RingedSpace.DeRham.coefficients
        (terminal.from X).toLRSHom.toShHom))).map
    ((DeRham.restriction
      (RingedSpace.DeRham.structureMap
        (terminal.from X).toLRSHom.toShHom)).map
      ((formExteriorIso (terminal.from X) p).hom ≫
        absoluteToRelativeForm g p ≫ (formExteriorIso g p).inv))

end AlgebraicGeometry.Scheme.RelativeDifferentials
