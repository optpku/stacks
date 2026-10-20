/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DGCup
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PushforwardTensor
@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open RingedSite.Hom
-- Local instance justification (defeq pin): the unit and tensor-wedge maps use the canonical derived category of the coefficient sheaf presentation.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.DeRham.CanonicalAction
variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- Coefficient-module global sections have pointwise right-derived values computed
on K-injective resolutions in the Grothendieck category of module sheaves. -/
theorem globalSections_hasPointwiseRightDerived :
    (moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).HasPointwiseRightDerivedFunctor
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) := sorry

-- Local instance justification (defeq pin): select the canonical pointwise-derived global-sections construction to form its shift comparison.
attribute [local instance] globalSections_hasPointwiseRightDerived

/-- The shift comparison for derived coefficient global sections is the total-derived one. -/
abbrev globalCommShift :
    (moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).CommShift ℤ :=
  Functor.totalRightDerived_commShift
    (moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))

-- Local instance justification (defeq pin): the regular DG-module action uses this specified derived-global-sections shift, never a caller-supplied choice.
attribute [local instance] globalCommShift

/-- The shifted action obtained by forgetting the regular DG-module lift of a class. -/
abbrev map (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (DerivedPushforward.derivedComplex p) (DerivedPushforward.derivedComplex p) n :=
  ClassAction.map p n ξ

/-- The canonical cohomology cup is the Yoneda product on regular right-DG-module lifts. -/
abbrev cup (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) : cohomology p (n + m) :=
  ClassAction.yonedaCup p n m ξ η

/-- The morphism induced on cohomology by the canonical action. -/
abbrev onCohomology (n m : ℤ) (ξ : cohomology p n) :
    cohomology p m ⟶ cohomology p (n + m) :=
  ClassAction.onCohomology p n m ξ

/-- The canonical action induces cup multiplication on cohomology. -/
theorem onCohomology_apply (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    (onCohomology p n m ξ).hom η = cup p n m ξ η :=
  ClassAction.onCohomology_apply_yonedaCup p n m ξ η

-- Local instance justification (defeq pin): every tensor occurrence uses the coefficient-sheaf total-left-derived bifunctor constructed in CanonicalTensor.
attribute [local instance] CanonicalTensor.hasCoefficientDerivedTensor

/-- Right-DG-module linearity of the regular-module lift identifies its underlying
action with left multiplication for the localized wedge multiplication. -/
theorem action_wedge_square (n : ℤ) (ξ : cohomology p n) :
    CommSq (CanonicalTensor.multiplication p)
      ((CanonicalTensor.tensor p).map (Prod.mkHom (map p n ξ) (𝟙 _)))
      (map p n ξ)
      ((CanonicalTensor.shiftFirst p (DerivedPushforward.derivedComplex p)
        (DerivedPushforward.derivedComplex p) n).hom ≫
        (CanonicalTensor.multiplication p)⟦n⟧') := sorry

/-- The coefficient unit complex concentrated in degree zero. -/
abbrev unitComplex := 𝟙_ (CochainComplex (RingedSpace.DeRham.Modules p.toLRSHom.toShHom) ℤ)

/-- The localized coefficient unit, with the same quotient presentation as de Rham cohomology. -/
abbrev unitObject := DerivedCategory.Qh.obj
  ((HomotopyCategory.quotient (RingedSpace.DeRham.Modules p.toLRSHom.toShHom) (up ℤ)).obj
    (unitComplex p))

/-- The localized constant-one cochain map into the de Rham complex. -/
def unitMap : unitObject p ⟶ DerivedPushforward.derivedComplex p :=
  DerivedCategory.Qh.map
    ((HomotopyCategory.quotient (RingedSpace.DeRham.Modules p.toLRSHom.toShHom) (up ℤ)).map
      (SheafOfModules.RingedSite.DifferentialGradedAlgebra.oneHom (deRhamDGA p)))

/-- Tensoring with the coefficient unit computes derived tensor without resolving the other
factor: the unit complex is K-flat. This assertion concerns only the unit, not arbitrary complexes. -/
theorem unitTensorCounit_isIso : IsIso
    (DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex
      (unitComplex p) (extendedDeRhamComplex p)) := sorry

-- Local instance justification (defeq pin): only the counit with the K-flat coefficient unit is inverted.
attribute [local instance] unitTensorCounit_isIso

/-- The inverse left-unit map obtained from the ordinary unitor and the unit-specific derived
tensor counit. The de Rham complex is not assumed K-flat. -/
def leftUnitInverse : DerivedPushforward.derivedComplex p ⟶
    (CanonicalTensor.tensor p).obj (unitObject p, DerivedPushforward.derivedComplex p) :=
  (DerivedCategory.quotientCompQhIso
    (RingedSpace.DeRham.Modules p.toLRSHom.toShHom)).hom.app (extendedDeRhamComplex p) ≫
  DerivedCategory.Q.map (λ_ (extendedDeRhamComplex p)).inv ≫
  inv (DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex
    (unitComplex p) (extendedDeRhamComplex p))

/-- Insert the constant-one class in the first factor of derived de Rham tensor. -/
def unitInsertion : DerivedPushforward.derivedComplex p ⟶
    (CanonicalTensor.tensor p).obj
      (DerivedPushforward.derivedComplex p, DerivedPushforward.derivedComplex p) :=
  leftUnitInverse p ≫ (CanonicalTensor.tensor p).map (Prod.mkHom (unitMap p) (𝟙 _))

/-- Counit naturality and the ordinary wedge left-unit law imply the derived left-unit law. -/
theorem unitInsertion_multiplication :
    unitInsertion p ≫ CanonicalTensor.multiplication p = 𝟙 _ := sorry

/-- The coefficient-unit representative of a class, obtained by evaluating its specified
regular-DG-module action on the constant-one cochain map. -/
def unitClass (n : ℤ) (ξ : cohomology p n) :
    unitObject p ⟶ (DerivedPushforward.derivedComplex p)⟦n⟧ :=
  unitMap p ≫ map p n ξ

/-- Left cup action formed with the coefficient-unit representative, the actual derived
tensor bifunctor, its first-factor shift, and the counit-and-wedge multiplication. -/
def wedgeMap (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (DerivedPushforward.derivedComplex p) (DerivedPushforward.derivedComplex p) n :=
  leftUnitInverse p ≫
  (CanonicalTensor.tensor p).map (Prod.mkHom (unitClass p n ξ) (𝟙 _)) ≫
  (CanonicalTensor.shiftFirst p (DerivedPushforward.derivedComplex p)
    (DerivedPushforward.derivedComplex p) n).hom ≫
  (CanonicalTensor.multiplication p)⟦n⟧'

/-- Functoriality factors tensor multiplication by a class through insertion of the unit. -/
theorem wedgeMap_eq (n : ℤ) (ξ : cohomology p n) :
    wedgeMap p n ξ = unitInsertion p ≫
      (CanonicalTensor.tensor p).map (Prod.mkHom (map p n ξ) (𝟙 _)) ≫
      (CanonicalTensor.shiftFirst p (DerivedPushforward.derivedComplex p)
        (DerivedPushforward.derivedComplex p) n).hom ≫
      (CanonicalTensor.multiplication p)⟦n⟧' := by
  have h : (CanonicalTensor.tensor p).map
      (Prod.mkHom (unitMap p ≫ map p n ξ) (𝟙 (DerivedPushforward.derivedComplex p))) =
      (CanonicalTensor.tensor p).map (Prod.mkHom (unitMap p) (𝟙 _)) ≫
      (CanonicalTensor.tensor p).map (Prod.mkHom (map p n ξ) (𝟙 _)) := by
    simpa using (CanonicalTensor.tensor p).map_comp
      (Prod.mkHom (unitMap p) (𝟙 (DerivedPushforward.derivedComplex p)))
      (Prod.mkHom (map p n ξ) (𝟙 (DerivedPushforward.derivedComplex p)))
  simp only [wedgeMap, unitClass, unitInsertion, h, Category.assoc]

/-- Derived right-module linearity and the left-unit law identify tensor-wedge action
with the action obtained by forgetting the regular DG-module lift. -/
theorem wedgeMap_eq_map (n : ℤ) (ξ : cohomology p n) :
    wedgeMap p n ξ = map p n ξ := by
  rw [wedgeMap_eq]
  have h := (action_wedge_square p n ξ).w
  rw [← h, ← Category.assoc, unitInsertion_multiplication, Category.id_comp]

/-- The hypercohomology cup obtained by applying the specified derived global sections
and homology shift to the derived-tensor counit-and-wedge action. -/
def rgammaWedgeCup (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    cohomology p (n + m) :=
  ((DerivedCategory.homologyFunctor (coefficientModules p) 0).shiftMap
    ((moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).shiftedHomMap
        (Iso.refl _) (Iso.refl _) n (wedgeMap p n ξ)) m (n + m) rfl).hom η

/-- The regular-DG Yoneda cup agrees with the actual derived-global-sections tensor-wedge cup. -/
theorem cup_eq_rgammaWedgeCup (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    cup p n m ξ η = rgammaWedgeCup p n m ξ η := by
  rw [rgammaWedgeCup, wedgeMap_eq_map]
  exact (onCohomology_apply p n m ξ η).symm

/-- Bilinearity of the Yoneda cup product over the global coefficient ring. -/
def cupBilinear (n m : ℤ) :
    cohomology p n →ₗ[coefficientRing p] cohomology p m →ₗ[coefficientRing p]
      cohomology p (n + m) :=
  let h :
      (∀ ξ η₁ η₂, cup p n m ξ (η₁ + η₂) = cup p n m ξ η₁ + cup p n m ξ η₂) ∧
        (∀ ξ a η, cup p n m ξ (a • η) = a • cup p n m ξ η) ∧
        (∀ ξ₁ ξ₂ η, cup p n m (ξ₁ + ξ₂) η = cup p n m ξ₁ η + cup p n m ξ₂ η) ∧
        (∀ a ξ η, cup p n m (a • ξ) η = a • cup p n m ξ η) := sorry
  { toFun := fun ξ =>
      { toFun := cup p n m ξ
        map_add' := fun η₁ η₂ => h.1 ξ η₁ η₂
        map_smul' := fun a η => h.2.1 ξ a η }
    map_add' := fun ξ₁ ξ₂ => LinearMap.ext fun η => h.2.2.1 ξ₁ ξ₂ η
    map_smul' := fun a ξ => LinearMap.ext fun η => h.2.2.2 a ξ η }

/-- The canonical hypercohomology cup morphism obtained from the bilinear DG Yoneda product. -/
def cupMorphism (n m : ℤ) :
    cohomology p n ⊗ cohomology p m ⟶ cohomology p (n + m) :=
  ModuleCat.ofHom (TensorProduct.lift (cupBilinear p n m))

/-- Evaluating the cup morphism on a pure tensor gives the DG Yoneda cup operation. -/
theorem cupMorphism_apply (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    (cupMorphism p n m).hom (ξ ⊗ₜ η) = cup p n m ξ η := rfl

/-- The bilinear cup used by consumers evaluates to the derived-global-sections wedge cup. -/
theorem cupMorphism_apply_rgammaWedgeCup (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    (cupMorphism p n m).hom (ξ ⊗ₜ η) = rgammaWedgeCup p n m ξ η :=
  (cupMorphism_apply p n m ξ η).trans (cup_eq_rgammaWedgeCup p n m ξ η)

/-- The action retains its specified right-DG-module lift. -/
theorem lifts (n : ℤ) (ξ : cohomology p n) :
    (ClassAction.forget p).shiftedHomMap (ClassAction.dgObjectIso p) (ClassAction.dgObjectIso p) n
      (ClassAction.dgLift p n ξ) = map p n ξ := ClassAction.lifts p n ξ

/-- Evaluation of the DG lift on the unit is the original class. -/
theorem one (n : ℤ) (ξ : cohomology p n) :
    ClassAction.valueAtOne p n (ClassAction.dgLift p n ξ) = ξ := ClassAction.one p n ξ

/-- The action is uniquely characterized by its DG lift and unit value. -/
theorem characterization (n : ℤ) (ξ : cohomology p n)
    (φ : ShiftedHom (DerivedPushforward.derivedComplex p) (DerivedPushforward.derivedComplex p) n) :
    φ = map p n ξ ↔
      ∃ ψ : ShiftedHom (ClassAction.dgObject p) (ClassAction.dgObject p) n,
        (ClassAction.forget p).shiftedHomMap (ClassAction.dgObjectIso p) (ClassAction.dgObjectIso p) n ψ = φ ∧
          ClassAction.valueAtOne p n ψ = ξ := ClassAction.characterization p n ξ φ

-- Local instance justification (defeq pin): direct images use the specified coefficient morphism's total-derived construction and shift, not a new ambient tensor or adjunction choice.
attribute [local instance] CanonicalTensor.coefficientPushforward_hasRightDerived
  CanonicalTensor.pushforwardCommShift

/-- The canonical open restriction map on the de Rham object. -/
abbrev restriction (U : X.Opens) := ClassAction.ordinaryRestriction p U

/-- The shifted action of the restricted class on the derived restriction target. -/
abbrev restrictedMap (U : X.Opens) (n : ℤ) (ξ : cohomology p n) :=
  ClassAction.restrictedMap p U n ξ

/-- The canonical action commutes with open restriction. -/
theorem restrict (U : X.Opens) (n : ℤ) (ξ : cohomology p n) :
    CommSq (map p n ξ) (restriction p U)
      ((shiftFunctor _ n).map (restriction p U)) (restrictedMap p U n ξ) :=
  ClassAction.restrict p U n ξ

variable {Y T : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ T} {h : S ⟶ T}
variable (sq : CommSq f p q h)

/-- The direct image of the relative de Rham complex in the target coefficient category. -/
abbrev pushedObject := (CanonicalTensor.pushforward sq).obj (DerivedPushforward.derivedComplex p)

/-- The shifted class action after the specified derived direct image. -/
def pushedMap (n : ℤ) (ξ : cohomology p n) :
    ShiftedHom (pushedObject p sq) (pushedObject p sq) n :=
  (CanonicalTensor.pushforward sq).shiftedHomMap (Iso.refl _) (Iso.refl _) n (map p n ξ)

/-- The lower cup arrow is the derived first-factor shift comparison followed by
the shift of the specified counit-and-wedge cup product. -/
def shiftedCup (n : ℤ) :
    (CanonicalTensor.tensor q).obj ((pushedObject p sq)⟦n⟧, pushedObject p sq) ⟶
      (pushedObject p sq)⟦n⟧ :=
  (CanonicalTensor.shiftFirst q (pushedObject p sq) (pushedObject p sq) n).hom ≫
    (CanonicalTensor.cupProduct sq)⟦n⟧'

/-- Right-DG-module linearity, the derived adjunction mate, and tensor naturality
give compatibility of class action with relative derived cup multiplication. -/
theorem pushforwardCupSquare (n : ℤ) (ξ : cohomology p n) :
    CommSq (CanonicalTensor.cupProduct sq)
      ((CanonicalTensor.tensor q).map (Prod.mkHom (pushedMap p sq n ξ) (𝟙 _)))
      (pushedMap p sq n ξ) (shiftedCup p sq n) := sorry

/-- Doubling a natural successor increases its integer degree by two. -/
theorem twiceSuccDegree (degree : ℕ) :
    2 * (degree : ℤ) + 2 = 2 * ((degree + 1 : ℕ) : ℤ) := sorry

/-- The cup powers of a degree-two class, starting with the cohomological unit. -/
def evenPower (cohomologyClass : cohomology p 2) :
    (degree : ℕ) → cohomology p (2 * (degree : ℤ))
  | 0 => ClassAction.cohomologyOneCanonical p
  | degree + 1 =>
      (eqToHom (congrArg (cohomology p) (twiceSuccDegree degree))).hom
        ((cupMorphism p (2 * (degree : ℤ)) 2).hom
          (evenPower cohomologyClass degree ⊗ₜ cohomologyClass))

/-- The integer degree accumulated by iterating a degree-two action. -/
def evenDegree : ℕ → ℤ
  | 0 => 0
  | degree + 1 => 2 + evenDegree degree

/-- The degree of a degree-two action iterated `degree` times is `2 * degree`. -/
theorem evenDegree_eq (degree : ℕ) : evenDegree degree = 2 * (degree : ℤ) := sorry

/-- Explicit recursive iteration of a degree-two shifted endomorphism. -/
def iterateDegreeTwo {C : Type*} [Category C] [HasShift C ℤ]
    {object : C} (action : ShiftedHom object object (2 : ℤ)) :
    (degree : ℕ) → ShiftedHom object object (evenDegree degree)
  | 0 => ShiftedHom.mk₀ 0 rfl (𝟙 object)
  | degree + 1 => (iterateDegreeTwo action degree).comp action rfl

end AlgebraicGeometry.Scheme.DeRham.CanonicalAction
