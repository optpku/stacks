/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Ringed

/-!
# Naive differentials on `C_{X/Λ}`

For a ring `Λ` and an algebraic space `X` over `Spec Λ`, this file constructs the
constant coefficient sheaf, its map to the structure sheaf, and the relative
differentials and their scalar extension to the pulled-back structure sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- Weak sheafification of commutative ring sheaves on `C_{X/Λ}`. -/
instance topology_hasWeakSheafify_commRing :
    HasWeakSheafify (topology Λ X) CommRingCat.{u} :=
  sorry

/-- Weak sheafification of lifted commutative ring sheaves on `C_{X/Λ}`. -/
instance topology_hasWeakSheafify_commRing_succ :
    HasWeakSheafify (topology Λ X) CommRingCat.{u + 1} :=
  sorry

/-- Weak sheafification of lifted abelian groups on `C_{X/Λ}`. -/
instance topology_hasWeakSheafify_addCommGrp_succ :
    HasWeakSheafify (topology Λ X) AddCommGrpCat.{u + 1} :=
  sorry

/-- Locally bijective morphisms are the weak equivalences for lifted abelian groups on
`C_{X/Λ}`. -/
instance topology_WEqualsLocallyBijective_addCommGrp_succ :
    (topology Λ X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Restriction of scalars of lifted module sheaves on `C_{X/Λ}` is a right adjoint. -/
instance topology_restrictScalars_isRightAdjoint
    {R R' : Sheaf (topology Λ X) RingCat.{u + 1}} (α : R ⟶ R') :
    (SheafOfModules.restrictScalars.{u + 1} α).IsRightAdjoint :=
  sorry

/-- The constant sheaf `underline{Λ}` on `C_{X/Λ}`. -/
def constSheaf : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (constantSheaf (topology Λ X) CommRingCat.{u + 1}).obj
    (CommRingCat.universeLift.{u, u + 1}.obj Λ)

/-- `constSheaf` is the constant sheaf with value `Λ`. -/
theorem constSheaf_eq :
    constSheaf Λ X = (constantSheaf (topology Λ X) CommRingCat.{u + 1}).obj
      (CommRingCat.universeLift.{u, u + 1}.obj Λ) :=
  rfl

/-- The universe-lifted constant sheaf `underline{Λ}` on `C_{X/Λ}`. -/
def constSheafLift : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (constantSheaf (topology Λ X) CommRingCat.{u + 1}).obj
    (CommRingCat.universeLift.{u, u + 1}.obj Λ)

/-- `constSheafLift` is the constant sheaf on the universe lift of `Λ`. -/
theorem constSheafLift_eq :
    constSheafLift Λ X =
      (constantSheaf (topology Λ X) CommRingCat.{u + 1}).obj
        (CommRingCat.universeLift.{u, u + 1}.obj Λ) :=
  rfl

/-- Component of the constant-to-structure map before sheafification at `(U ⟶ A)`. -/
def constToOPresheafApp (x : (category Λ X)ᵒᵖ) :
    ((Functor.const (category Λ X)ᵒᵖ).obj
        (CommRingCat.universeLift.{u, u + 1}.obj Λ)).obj x ⟶
      (structurePresheaf Λ X).obj x :=
  (CommRingCat.universeLift.{u, u + 1}).map
    ((Scheme.ΓSpecIso Λ).inv ≫ (unop x).right.obj.hom.appTop)

/-- Unfolding of `constToOPresheafApp`. -/
theorem constToOPresheafApp_eq (x : (category Λ X)ᵒᵖ) :
    constToOPresheafApp Λ X x =
      (CommRingCat.universeLift.{u, u + 1}).map
        ((Scheme.ΓSpecIso Λ).inv ≫ (unop x).right.obj.hom.appTop) :=
  rfl

/-- The constant-to-structure map of presheaves, before sheafification. -/
def constToOPresheaf :
    (Functor.const (category Λ X)ᵒᵖ).obj
      (CommRingCat.universeLift.{u, u + 1}.obj Λ) ⟶ structurePresheaf Λ X where
  app := constToOPresheafApp Λ X
  naturality _ _ _ := sorry

/-- Components of `constToOPresheaf` are `constToOPresheafApp`. -/
theorem constToOPresheaf_app (x : (category Λ X)ᵒᵖ) :
    (constToOPresheaf Λ X).app x = constToOPresheafApp Λ X x :=
  rfl

/-- The algebra map `underline{Λ} ⟶ O` on `C_{X/Λ}`. -/
def constToO : constSheaf Λ X ⟶ structureSheaf Λ X :=
  ((sheafificationAdjunction (topology Λ X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const _).obj (CommRingCat.universeLift.{u, u + 1}.obj Λ))
      (structureSheaf Λ X)).symm
    (constToOPresheaf Λ X ≫ structureSheafUnit Λ X)

/-- `constToO` is the sheafification adjunct of `constToOPresheaf`. -/
theorem constToO_eq :
    constToO Λ X =
      ((sheafificationAdjunction (topology Λ X) CommRingCat.{u + 1}).homEquiv
          ((Functor.const _).obj (CommRingCat.universeLift.{u, u + 1}.obj Λ))
          (structureSheaf Λ X)).symm
        (constToOPresheaf Λ X ≫ structureSheafUnit Λ X) :=
  rfl

/-- The component of `constToOPresheaf` at `(U ⟶ A)` is the structure map
`Λ ⟶ Γ(A, 𝒪_A)`. -/
theorem constToO_app (x : category Λ X) :
    (constToOPresheaf Λ X).app (op x) =
      (CommRingCat.universeLift.{u, u + 1}).map
        ((Scheme.ΓSpecIso Λ).inv ≫ x.right.obj.hom.appTop) :=
  rfl

/-- Component of the lifted constant-to-structure presheaf map at `(U ⟶ A)`. -/
def constToOLiftPresheafApp (x : (category Λ X)ᵒᵖ) :
    ((Functor.const (category Λ X)ᵒᵖ).obj
        (CommRingCat.universeLift.{u, u + 1}.obj Λ)).obj x ⟶
      (structurePresheafLift Λ X).obj x :=
  (CommRingCat.universeLift.{u, u + 1}).map
    ((Scheme.ΓSpecIso Λ).inv ≫ (unop x).right.obj.hom.appTop)

/-- Unfolding of `constToOLiftPresheafApp`. -/
theorem constToOLiftPresheafApp_eq (x : (category Λ X)ᵒᵖ) :
    constToOLiftPresheafApp Λ X x =
      (CommRingCat.universeLift.{u, u + 1}).map
        ((Scheme.ΓSpecIso Λ).inv ≫ (unop x).right.obj.hom.appTop) :=
  rfl

/-- The lifted constant-to-structure map of presheaves, before sheafification. -/
def constToOLiftPresheaf :
    (Functor.const (category Λ X)ᵒᵖ).obj
        (CommRingCat.universeLift.{u, u + 1}.obj Λ) ⟶
      structurePresheafLift Λ X where
  app := constToOLiftPresheafApp Λ X
  naturality _ _ _ := sorry

/-- Components of `constToOLiftPresheaf` are `constToOLiftPresheafApp`. -/
theorem constToOLiftPresheaf_app (x : (category Λ X)ᵒᵖ) :
    (constToOLiftPresheaf Λ X).app x =
      constToOLiftPresheafApp Λ X x :=
  rfl

/-- The lifted algebra map `underline{Λ} ⟶ O` on `C_{X/Λ}`. -/
def constToOLift : constSheafLift Λ X ⟶ structureSheafLift Λ X :=
  ((sheafificationAdjunction (topology Λ X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const _).obj (CommRingCat.universeLift.{u, u + 1}.obj Λ))
      (structureSheafLift Λ X)).symm
    (constToOLiftPresheaf Λ X ≫ structureSheafUnit Λ X)

/-- `constToOLift` is the sheafification adjunct of `constToOLiftPresheaf`. -/
theorem constToOLift_eq :
    constToOLift Λ X =
      ((sheafificationAdjunction (topology Λ X) CommRingCat.{u + 1}).homEquiv
          ((Functor.const _).obj (CommRingCat.universeLift.{u, u + 1}.obj Λ))
          (structureSheafLift Λ X)).symm
        (constToOLiftPresheaf Λ X ≫ structureSheafUnit Λ X) :=
  rfl

/-- The component of `constToOLiftPresheaf` at `(U ⟶ A)` is the universe lift of
`Λ ⟶ Γ(A, 𝒪_A)`. -/
theorem constToOLift_app (x : category Λ X) :
    (constToOLiftPresheaf Λ X).app (op x) =
      (CommRingCat.universeLift.{u, u + 1}).map
        ((Scheme.ΓSpecIso Λ).inv ≫ x.right.obj.hom.appTop) :=
  rfl

/-- The sheaf `Ω_{O/underline{Λ}}` of relative differentials on `C_{X/Λ}`. -/
def omega : SheafOfModules.{u + 1}
    (ringSheaf.{u + 1, u, u + 1} (topology Λ X) (structureSheafLift Λ X)) :=
  relativeDifferentials.{u + 1, u, u + 1} (constToOLift Λ X)

/-- `omega` is `Ω` of the lifted algebra map `underline{Λ} ⟶ O`. -/
theorem omega_eq :
    omega Λ X = relativeDifferentials.{u + 1, u, u + 1} (constToOLift Λ X) :=
  rfl

/-- The differentials sheaf is evaluated after extending the presheaf of affine-target
Kähler differentials along the canonical structure-sheaf unit and sheafifying. -/
theorem omega_obj (x : category Λ X) :
    IsIsomorphic ((omega Λ X).val.obj (op x))
      (((PresheafOfModules.sheafification.{u + 1}
          (𝟙 (ringSheaf.{u + 1, u, u + 1} (topology Λ X)
            (structureSheafLift Λ X)).obj)).obj
          ((PresheafOfModules.SameSiteTensorExtension.functor
              (structureSheafUnit Λ X)).obj
            (relativeDifferentials' (constToOLiftPresheaf Λ X)))).val.obj (op x)) :=
  sorry

/-- Restriction of the naive-differentials presheaf along a morphism of `C_{X/Λ}` is
Kähler base change of the corresponding ring maps `Λ ⟶ Γ(A)` and `Λ ⟶ Γ(A')`. -/
theorem omega_map {x y : category Λ X} (f : x ⟶ y) :
    (relativeDifferentials' (constToOLiftPresheaf Λ X)).map (op f) =
      CommRingCat.KaehlerDifferential.map
        ((constToOLiftPresheaf Λ X).naturality (op f)) :=
  rfl

/-- `Ω_{O/underline{Λ}}` is a flat `O`-module, since each affine vertex is a polynomial
`Λ`-algebra. -/
instance omega_isFlat :
    IsFlat.{u + 1, u, u + 1} (structureSheafLift Λ X) (omega Λ X) :=
  sorry

/-- The sheaf `Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X` on `C_{X/Λ}`. -/
def omegaTensor :
    SheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u, u + 1} (topology Λ X) (underlineSheafLift Λ X)) :=
  (SheafOfModules.ChangeOfRings.extendScalars.{u + 1, u, u + 1, u + 1}
      (ringSheafMap.{u + 1, u, u + 1} (structureSheafMapLift Λ X))).obj (omega Λ X)

/-- `omegaTensor` is extension of scalars of `omega` along `i♯`. -/
theorem omegaTensor_eq :
    omegaTensor Λ X =
      (SheafOfModules.ChangeOfRings.extendScalars.{u + 1, u, u + 1, u + 1}
          (ringSheafMap.{u + 1, u, u + 1} (structureSheafMapLift Λ X))).obj
        (omega Λ X) :=
  rfl

/-- The tensor-differentials sheaf is evaluated after extending affine-target Kähler
differentials along the raw structure map followed by the pulled-back structure-sheaf unit,
and then sheafifying. -/
theorem omegaTensor_obj (x : category Λ X) :
    IsIsomorphic ((omegaTensor Λ X).val.obj (op x))
      (((PresheafOfModules.sheafification.{u + 1}
          (𝟙 (ringSheaf.{u + 1, u, u + 1} (topology Λ X)
            (underlineSheafLift Λ X)).obj)).obj
          ((PresheafOfModules.SameSiteTensorExtension.functor
              (structurePresheafMapLift Λ X ≫ underlineSheafUnit Λ X)).obj
            (relativeDifferentials' (constToOLiftPresheaf Λ X)))).val.obj (op x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
