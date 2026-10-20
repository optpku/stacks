/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ExactSequence
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Integral
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle

/-!
# Total Chern classes on vector-bundle K-theory

Total Chern classes are packaged as central units in the completed nonnegative
Chow ring and descended through the short-exact relations defining vector-bundle `K₀`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The completed total Chern-class value of a finite locally free module. -/
def totalChernValue (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ChowCohomology.Nonnegative.Completion δ p :=
  fun i ↦ classes.component E.obj i

/-- A coefficient of the completed total Chern-class value is the corresponding
Chern-class component. -/
theorem totalChernValue_apply (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℕ) :
    totalChernValue δ p classes E i = classes.component E.obj i := sorry

/-- The constant coefficient of a total Chern-class value is one. -/
theorem totalChernValue_zero (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    totalChernValue δ p classes E 0 = ChowCohomology.one δ p := sorry

/-- Every total Chern-class value is central in the completed Chow ring. -/
theorem totalChernValue_mem_center (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    totalChernValue δ p classes E ∈
      Set.center (ChowCohomology.Nonnegative.Completion δ p) := sorry

/-- Total Chern-class values satisfy the Whitney formula on short exact sequences. -/
theorem totalChernValue_shortExact (classes : ChernClass.Theory δ p)
    (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (hC : C.ShortExact) :
    (fun i ↦ classes.component C.X₂ i) =
      ChowCohomology.Nonnegative.Completion.mul δ p
        (fun i ↦ classes.component C.X₁ i) (fun i ↦ classes.component C.X₃ i) := sorry

/-- Package a total Chern-class value as a unit of the center of the completed Chow ring. -/
def totalChernUnitValue (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (Submonoid.center (ChowCohomology.Nonnegative.Completion δ p))ˣ :=
  ChowCohomology.Nonnegative.Completion.unitOf δ p (totalChernValue δ p classes E)
    (totalChernValue_zero δ p classes E) (totalChernValue_mem_center δ p classes E)

/-- The underlying completed class of `totalChernUnitValue` is `totalChernValue`. -/
theorem totalChernUnitValue_val (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (totalChernUnitValue δ p classes E).val.val = totalChernValue δ p classes E := sorry

/-- Short-exact relations lie in the kernel of the free additive lift of the
central-unit-valued total Chern class. -/
theorem relations_le_ker_totalChernClass (classes : ChernClass.Theory δ p) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift (fun E : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦
        Additive.ofMul (totalChernUnitValue δ p classes E))).ker := sorry

/-- The total Chern class as an additive homomorphism into the additive form of
the commutative group of central units. -/
def totalChernClassHom (classes : ChernClass.Theory δ p) :
    VectorBundleK0 X →+
      Additive ((Submonoid.center (ChowCohomology.Nonnegative.Completion δ p))ˣ) :=
  ObjectProperty.GrothendieckGroup.lift
    (fun E ↦ Additive.ofMul (totalChernUnitValue δ p classes E))
    (relations_le_ker_totalChernClass δ p classes)

/-- The bundled total Chern-class map takes a generator to its packaged total class. -/
theorem totalChernClassHom_of (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    totalChernClassHom δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      Additive.ofMul (totalChernUnitValue δ p classes E) := sorry

/-- The product-valued total Chern-class map obtained by forgetting the central-unit packaging. -/
def totalChernClass (classes : ChernClass.Theory δ p) (a : VectorBundleK0 X) :
    ChowCohomology.Nonnegative.Completion δ p :=
  (totalChernClassHom δ p classes a).toMul.val.val

/-- A vector-bundle generator maps to its completed total Chern-class value. -/
theorem totalChernClass_of (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    totalChernClass δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      totalChernValue δ p classes E := sorry

/-- On a vector-bundle generator, every coefficient of the total Chern class is
the corresponding Chern-class component. -/
theorem totalChernClass_apply_of (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) (i : ℕ) :
    totalChernClass δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) i =
      classes.component E.obj i := sorry

/-- The zero class maps to the convolution unit. -/
theorem totalChernClass_zero (classes : ChernClass.Theory δ p) :
    totalChernClass δ p classes 0 = 1 := sorry

/-- Addition in vector-bundle `K₀` becomes convolution multiplication of total Chern classes. -/
theorem totalChernClass_add (classes : ChernClass.Theory δ p) (a b : VectorBundleK0 X) :
    totalChernClass δ p classes (a + b) =
      totalChernClass δ p classes a * totalChernClass δ p classes b := sorry

/-- Negation in vector-bundle `K₀` becomes formal inversion of total Chern classes. -/
theorem totalChernClass_neg (classes : ChernClass.Theory δ p) (a : VectorBundleK0 X) :
    totalChernClass δ p classes (-a) =
      ChowCohomology.Nonnegative.Completion.formalInverse δ p
        (totalChernClass δ p classes a) := sorry

/-- A negative vector-bundle generator maps to the formal inverse of its total Chern class. -/
theorem totalChernClass_neg_of (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    totalChernClass δ p classes
        (-ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      ChowCohomology.Nonnegative.Completion.formalInverse δ p
        (totalChernValue δ p classes E) := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
