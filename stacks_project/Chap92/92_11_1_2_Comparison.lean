/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import stacks_project.Chap92.«92_11_1_1_Comparison»
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Truncated comparison from a polynomial naive cotangent complex

This leaf owns the canonical morphism in `DerivedCategory (ModuleCat B)` from the two-term
complex `J/J² ⟶ Ω_{P/A} ⊗_P B` of a polynomial arrow `P ⟶ B` to `τ_{≥ -1} L_{B/A}`. The
morphism is the 08Q6 evaluation of that two-term complex on the standard polynomial
resolution, transported along the truncated mapping-cone identification with `τ_{≥ -1} L_{B/A}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open DerivedCategory.TStructure
open scoped Simplicial ZeroObject TensorProduct ChangeOfRings

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under
namespace CotangentComplex

open CommRingCat.Under.FreeAlgebra

/-- The conormal module `J/J² ⊗_P B` of a polynomial arrow `φ : A[E] ⟶ B`. -/
def naiveConormal (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} B.right :=
  (ModuleCat.extendScalars φ.right.hom).obj
    (ModuleCat.of ((functor A).obj E).right (RingHom.ker φ.right.hom).Cotangent)

/-- The module `Ω_{P/A} ⊗_P B` of a polynomial arrow, as a `B`-module. -/
def naiveDifferentials (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} B.right :=
  (ModuleCat.extendScalars φ.right.hom).obj
    (CommRingCat.KaehlerDifferential ((functor A).obj E).hom)

/-- Restriction of scalars of `Ω_{P/A} ⊗_P B` along `φ`. -/
def naiveDifferentialsRestrict (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} ((functor A).obj E).right :=
  (ModuleCat.restrictScalars φ.right.hom).obj (naiveDifferentials A B E φ)

/-- The kernel representative map `J ⟶ Ω_{P/A} ⊗_P B`. -/
def naiveDifferentialOnKer (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    RingHom.ker φ.right.hom →ₗ[((functor A).obj E).right]
      (naiveDifferentialsRestrict A B E φ) where
  toFun j :=
    (1 : B.right) ⊗ₜ[((functor A).obj E).right, φ.right.hom]
      (CommRingCat.KaehlerDifferential.d (j : RingHom.ker φ.right.hom).1)
  map_add' := sorry
  map_smul' := sorry

/-- Products in the kernel are sent to zero by `naiveDifferentialOnKer`. -/
theorem naiveDifferentialOnKer_mul (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) (x y : RingHom.ker φ.right.hom) :
    naiveDifferentialOnKer A B E φ (x * y) = 0 := sorry

/-- The kernel square as a submodule of the kernel. -/
abbrev naiveKerSquare (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    Submodule ((functor A).obj E).right (RingHom.ker φ.right.hom) :=
  (RingHom.ker φ.right.hom) • ⊤

/-- The kernel square is sent to zero by `naiveDifferentialOnKer`. -/
theorem naiveDifferentialOnKer_mem_square (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B)
    (x : RingHom.ker φ.right.hom) (hx : x ∈ naiveKerSquare A B E φ) :
    naiveDifferentialOnKer A B E φ x = 0 := sorry

/-- The `P`-module of `J/J²`. -/
def naiveConormalRestrict (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} ((functor A).obj E).right :=
  ModuleCat.of ((functor A).obj E).right (RingHom.ker φ.right.hom).Cotangent

/-- The `P`-linear map `J/J² ⟶ Ω_{P/A} ⊗_P B` on the conormal module. -/
def naiveDifferentialRestrict (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveConormalRestrict A B E φ ⟶ naiveDifferentialsRestrict A B E φ :=
  ConcreteCategory.ofHom
    { toFun := fun x =>
        Quotient.liftOn x (naiveDifferentialOnKer A B E φ)
          (fun a b h ↦ sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- The differential `J/J² ⊗_P B ⟶ Ω_{P/A} ⊗_P B` of a polynomial arrow. -/
def naiveDifferential (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveConormal A B E φ ⟶ naiveDifferentials A B E φ :=
  ((ModuleCat.extendRestrictScalarsAdj φ.right.hom).homEquiv _ _).symm
    (naiveDifferentialRestrict A B E φ)

/-- The two-term chain complex `J/J² ⟶ Ω_{P/A} ⊗_P B` of a polynomial arrow. -/
def naiveChain (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ChainComplex (ModuleCat.{u} B.right) ℕ :=
  ChainComplex.mk'
    (naiveDifferentials A B E φ)
    (naiveConormal A B E φ)
    (naiveDifferential A B E φ)
    (fun {_ _} _ ↦ ⟨0, 0, zero_comp⟩)

/-- The two-term cochain complex `(J/J² ⟶ Ω_{P/A} ⊗_P B)` in cohomological degrees `-1` and
`0`. -/
def naiveComplex (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : CochainComplex (ModuleCat.{u} B.right) ℤ :=
  (naiveChain A B E φ).extend ComplexShape.embeddingDownNat

/-- Identification of the degree-`0` term with `Ω_{P/A} ⊗_P B`. -/
def naiveComplex_X_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (naiveComplex A B E φ).X 0 ≅ naiveDifferentials A B E φ :=
  extendXIso (naiveChain A B E φ) ComplexShape.embeddingDownNat
    (rfl : ComplexShape.embeddingDownNat.f 0 = 0)

/-- Identification of the degree-`-1` term with `J/J² ⊗_P B`. -/
def naiveComplex_X_negOne (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (naiveComplex A B E φ).X (-1) ≅ naiveConormal A B E φ :=
  extendXIso (naiveChain A B E φ) ComplexShape.embeddingDownNat
    (rfl : ComplexShape.embeddingDownNat.f 1 = -1)

/-- Degree-`0` component of the truncated comparison, as a `B`-module map
`Ω_{P/A} ⊗_P B ⟶ Ω_{P₀/A} ⊗_{P₀} B`. -/
def truncGE_f_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveDifferentials A B E φ ⟶ (simplicialModule A B).obj (op ⦋0⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.right.hom).homEquiv _ _).symm
    (comparisonDifferentialsMap A B E φ ≫
      (ModuleCat.restrictScalars (toStandard A B E φ).right.hom).map
        ((ModuleCat.extendRestrictScalarsAdj
            (standardAugmentation A B (op ⦋0⦌)).hom).unit.app _) ≫
      (ModuleCat.restrictScalarsComp'
        (toStandard A B E φ).right.hom
        (standardAugmentation A B (op ⦋0⦌)).hom
        φ.right.hom
        (toStandard_comp_augmentation_hom A B E φ)).inv.app _)

/-- The `P_n`-module `Ker(P_n ⟶ B)/Ker(P_n ⟶ B)²`. -/
def standardNaiveConormalRestrict (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) : ModuleCat.{u} (standardTerm A B n).right :=
  ModuleCat.of (standardTerm A B n).right
    (RingHom.ker (standardAugmentation A B n).hom).Cotangent

/-- The `B`-module `J_n/J_n² ⊗_{P_n} B` of a standard-resolution term. -/
def standardNaiveConormal (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    ModuleCat.{u} B.right :=
  (ModuleCat.extendScalars (standardAugmentation A B n).hom).obj
    (standardNaiveConormalRestrict A B n)

/-- Restriction of scalars of `J_n/J_n² ⊗_{P_n} B` along a polynomial arrow `φ`. -/
def standardNaiveConormalRestrictAlong (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) (n : SimplexCategoryᵒᵖ) :
    ModuleCat.{u} ((functor A).obj E).right :=
  (ModuleCat.restrictScalars φ.right.hom).obj (standardNaiveConormal A B n)

/-- The kernel representative map `J ⟶ J_0/J_0² ⊗_{P_0} B` induced by `toStandard`. -/
def kerToStandardConormalLinear (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    RingHom.ker φ.right.hom →ₗ[((functor A).obj E).right]
      (standardNaiveConormalRestrictAlong A B E φ (op ⦋0⦌)) where
  toFun j :=
    (1 : B.right) ⊗ₜ[(standardTerm A B (op ⦋0⦌)).right,
        (standardAugmentation A B (op ⦋0⦌)).hom]
      (Ideal.toCotangent _
        ⟨(toStandard A B E φ).right j.1, toStandard_mem_ker A B E φ j⟩)
  map_add' := sorry
  map_smul' := sorry

/-- Products in the kernel are sent to zero by `kerToStandardConormalLinear`. -/
theorem kerToStandardConormalLinear_mul (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) (x y : RingHom.ker φ.right.hom) :
    kerToStandardConormalLinear A B E φ (x * y) = 0 := sorry

/-- The kernel square is sent to zero by `kerToStandardConormalLinear`. -/
theorem kerToStandardConormalLinear_mem_square (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B)
    (x : RingHom.ker φ.right.hom) (hx : x ∈ naiveKerSquare A B E φ) :
    kerToStandardConormalLinear A B E φ x = 0 := sorry

/-- The `P`-linear map `J/J² ⟶ J_0/J_0² ⊗_{P_0} B` induced by `toStandard`. -/
def conormalToStandardRestrict (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveConormalRestrict A B E φ ⟶
      standardNaiveConormalRestrictAlong A B E φ (op ⦋0⦌) :=
  ConcreteCategory.ofHom
    { toFun := fun x =>
        Quotient.liftOn x (kerToStandardConormalLinear A B E φ)
          (fun a b h ↦ sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`-1` evaluation component `J/J² ⊗_P B ⟶ J_0/J_0² ⊗_{P_0} B` along `toStandard`. -/
def conormalToStandard (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveConormal A B E φ ⟶ standardNaiveConormal A B (op ⦋0⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.right.hom).homEquiv _ _).symm
    (conormalToStandardRestrict A B E φ)

/-- The `P_n`-linear map on conormal modules induced by a simplicial operator. -/
def standardNaiveConormalRestrictMap (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    standardNaiveConormalRestrict A B n ⟶
      (ModuleCat.restrictScalars (standardMap A B φ).right.hom).obj
        (standardNaiveConormalRestrict A B m) :=
  ConcreteCategory.ofHom
    { toFun := fun x =>
        Quotient.liftOn x
          (fun j =>
            Ideal.toCotangent _
              ⟨(standardMap A B φ).right
                (j : RingHom.ker (standardAugmentation A B n).hom).1, sorry⟩)
          (fun a b h ↦ sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- The map of `B`-modules `J_n/J_n² ⊗_{P_n} B ⟶ J_m/J_m² ⊗_{P_m} B` induced by a simplicial
operator. -/
def standardNaiveConormalMap (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    standardNaiveConormal A B n ⟶ standardNaiveConormal A B m :=
  ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B n).hom).homEquiv _ _).symm
    (standardNaiveConormalRestrictMap A B φ ≫
      (ModuleCat.restrictScalars (standardMap A B φ).right.hom).map
        ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B m).hom).unit.app _) ≫
      (ModuleCat.restrictScalarsComp' (standardMap A B φ).right.hom
          (standardAugmentation A B m).hom (standardAugmentation A B n).hom
          (standardMap_comp_augmentation_hom A B φ)).inv.app _)

/-- The identity simplicial operator acts as the identity on `J_n/J_n² ⊗_{P_n} B`. -/
theorem standardNaiveConormalMap_id (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    standardNaiveConormalMap A B (𝟙 n) = 𝟙 _ := sorry

/-- Simplicial-operator composition is preserved on `J_n/J_n² ⊗_{P_n} B`. -/
theorem standardNaiveConormalMap_comp (A : CommRingCat.{u}) (B : Under A)
    {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k) :
    standardNaiveConormalMap A B (φ ≫ ψ) =
      standardNaiveConormalMap A B φ ≫ standardNaiveConormalMap A B ψ := sorry

/-- The simplicial `B`-module `J_n/J_n² ⊗_{P_n} B` of the standard polynomial resolution. -/
def naiveConormalSimplicial (A : CommRingCat.{u}) (B : Under A) :
    SimplicialObject (ModuleCat.{u} B.right) where
  obj n := standardNaiveConormal A B n
  map φ := standardNaiveConormalMap A B φ
  map_id n := standardNaiveConormalMap_id A B n
  map_comp φ ψ := standardNaiveConormalMap_comp A B φ ψ

/-- Degreewise, `naiveConormalSimplicial` is the base change of `J_n/J_n²`. -/
theorem naiveConormalSimplicial_obj (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (naiveConormalSimplicial A B).obj n = standardNaiveConormal A B n := sorry

/-- The `P_n`-linear differential `J_n/J_n² ⟶ Ω_{P_n/A} ⊗_{P_n} B` of a standard-resolution
term. -/
def standardNaiveConormalToDifferentialsRestrict (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    standardNaiveConormalRestrict A B n ⟶
      (ModuleCat.restrictScalars (standardAugmentation A B n).hom).obj
        ((simplicialModule A B).obj n) :=
  ConcreteCategory.ofHom
    { toFun := fun x =>
        Quotient.liftOn x
          (fun j =>
            (1 : B.right) ⊗ₜ[(standardTerm A B n).right, (standardAugmentation A B n).hom]
              (CommRingCat.KaehlerDifferential.d
                (j : RingHom.ker (standardAugmentation A B n).hom).1))
          (fun a b h ↦ sorry)
      map_add' := sorry
      map_smul' := sorry }

/-- The differential `J_n/J_n² ⊗_{P_n} B ⟶ Ω_{P_n/A} ⊗_{P_n} B` of a standard-resolution
term. -/
def standardNaiveConormalToDifferentials (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    standardNaiveConormal A B n ⟶ (simplicialModule A B).obj n :=
  ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B n).hom).homEquiv _ _).symm
    (standardNaiveConormalToDifferentialsRestrict A B n)

/-- The simplicial map `J_•/J_•² ⟶ Ω_{P_•/A} ⊗_{P_•} B` on the standard polynomial
resolution. -/
def naiveConormalSimplicialToOmega (A : CommRingCat.{u}) (B : Under A) :
    naiveConormalSimplicial A B ⟶ simplicialModule A B where
  app n := standardNaiveConormalToDifferentials A B n
  naturality _ _ _ := sorry

/-- The alternating-face chain complex of `J_n/J_n² ⊗_{P_n} B`. -/
def naiveConormalChain (A : CommRingCat.{u}) (B : Under A) :
    ChainComplex (ModuleCat.{u} B.right) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} B.right)).obj (naiveConormalSimplicial A B)

/-- The cochain complex of `B`-modules associated to `J_n/J_n² ⊗_{P_n} B`, placed in
nonpositive cohomological degrees. -/
def naiveConormalComplex (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} B.right) ℤ :=
  (naiveConormalChain A B).extend ComplexShape.embeddingDownNat

/-- Identification of the cohomological degree `-n` term of `naiveConormalComplex` with
`J_n/J_n² ⊗_{P_n} B`. -/
def naiveConormalComplex_X (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (naiveConormalComplex A B).X (-n) ≅ standardNaiveConormal A B (op ⦋n⦌) :=
  extendXIso (naiveConormalChain A B) ComplexShape.embeddingDownNat
    (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- Components of the cochain map `J_•/J_•² ⟶ L_{B/A}` of `B`-modules. -/
def naiveConormalToObj_f (A : CommRingCat.{u}) (B : Under A) :
    ∀ i : ℤ, (naiveConormalComplex A B).X i ⟶ (obj A B).X i
  | Int.ofNat 0 =>
      (naiveConormalComplex_X A B 0).hom ≫
        standardNaiveConormalToDifferentials A B (op ⦋0⦌) ≫ (objXIso A B 0).inv
  | Int.negSucc n =>
      (naiveConormalComplex_X A B (n + 1)).hom ≫
        standardNaiveConormalToDifferentials A B (op ⦋n + 1⦌) ≫ (objXIso A B (n + 1)).inv
  | Int.ofNat (_n + 1) => 0

/-- The cochain map `J_•/J_•² ⟶ L_{B/A}` of `B`-modules induced by `1 ⊗ d` on each
standard-resolution term. -/
def naiveConormalToObj (A : CommRingCat.{u}) (B : Under A) :
    naiveConormalComplex A B ⟶ obj A B where
  f := naiveConormalToObj_f A B
  comm' := sorry

/-- Degree `0` of `naiveConormalToObj` is `1 ⊗ d` on `J_0/J_0²`. -/
theorem naiveConormalToObj_f_zero (A : CommRingCat.{u}) (B : Under A) :
    (naiveConormalToObj A B).f 0 =
      (naiveConormalComplex_X A B 0).hom ≫
        standardNaiveConormalToDifferentials A B (op ⦋0⦌) ≫ (objXIso A B 0).inv := sorry

/-- The homotopy cofiber of `naiveConormalToObj` exists by biproducts in `ModuleCat`. -/
instance hasHomotopyCofiber_naiveConormalToObj (A : CommRingCat.{u}) (B : Under A) :
    HasHomotopyCofiber (naiveConormalToObj A B) := inferInstance

/-- The mapping cone of `J_•/J_•² ⟶ Ω(P_•)`, computing `Lπ_!(J/J² ⟶ Ω)` on the standard
polynomial resolution. -/
def evaluationCone (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} B.right) ℤ :=
  CochainComplex.mappingCone (naiveConormalToObj A B)

/-- Unfolding of `evaluationCone` as the mapping cone of `naiveConormalToObj`. -/
theorem evaluationCone_eq (A : CommRingCat.{u}) (B : Under A) :
    evaluationCone A B = CochainComplex.mappingCone (naiveConormalToObj A B) := sorry

/-- The inclusion of `L_{B/A}` into the mapping cone of `J_•/J_•² ⟶ Ω(P_•)`. -/
def evaluationInr (A : CommRingCat.{u}) (B : Under A) :
    obj A B ⟶ evaluationCone A B :=
  CochainComplex.mappingCone.inr (naiveConormalToObj A B)

/-- `evaluationInr` is the mapping-cone inclusion of the `Ω` rows. -/
theorem evaluationInr_eq (A : CommRingCat.{u}) (B : Under A) :
    evaluationInr A B = CochainComplex.mappingCone.inr (naiveConormalToObj A B) := sorry

/-- Naturality of `1 ⊗ d` along `toStandard` on conormal modules. -/
theorem conormalToStandard_comp_differentials (A : CommRingCat.{u}) (B : Under A)
    (E : Type u) (φ : (functor A).obj E ⟶ B) :
    conormalToStandard A B E φ ≫ standardNaiveConormalToDifferentials A B (op ⦋0⦌) =
      naiveDifferential A B E φ ≫ truncGE_f_zero A B E φ := sorry

/-- Components of the evaluation map from a polynomial arrow into the standard-resolution
mapping cone of `J/J² ⟶ Ω`. -/
def evaluationToCone_f (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    ∀ i : ℤ, (naiveComplex A B E φ).X i ⟶ (evaluationCone A B).X i :=
  fun i ↦
    if h0 : i = 0 then
      eqToHom (congrArg (naiveComplex A B E φ).X h0) ≫
        (naiveComplex_X_zero A B E φ).hom ≫
          truncGE_f_zero A B E φ ≫
            (objXIso A B 0).inv ≫
              (evaluationInr A B).f 0 ≫
                eqToHom (congrArg (evaluationCone A B).X h0.symm)
    else if h1 : i = -1 then
      eqToHom (congrArg (naiveComplex A B E φ).X h1) ≫
        (naiveComplex_X_negOne A B E φ).hom ≫
          conormalToStandard A B E φ ≫
            (naiveConormalComplex_X A B 0).inv ≫
              HomologicalComplex.homotopyCofiber.inlX (naiveConormalToObj A B) 0 (-1)
                up_rel_negOne_zero ≫
                eqToHom (congrArg (evaluationCone A B).X h1.symm)
    else
      0

/-- The cochain map evaluating `J/J² ⟶ Ω` at a polynomial presentation `φ` and sending the
result to the standard-resolution computation of `Lπ_!(J/J² ⟶ Ω)`. Degree `0` is the map of
Kähler differentials along `toStandard`; degree `-1` is the induced map on conormal modules
`J/J² ⟶ J_0/J_0²`. -/
def evaluationToCone (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveComplex A B E φ ⟶ evaluationCone A B where
  f := evaluationToCone_f A B E φ
  comm' := sorry

/-- Degree `0` of `evaluationToCone` is `truncGE_f_zero` followed by `evaluationInr`. -/
theorem evaluationToCone_f_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (evaluationToCone A B E φ).f 0 =
      (naiveComplex_X_zero A B E φ).hom ≫
        truncGE_f_zero A B E φ ≫ (objXIso A B 0).inv ≫ (evaluationInr A B).f 0 := sorry

end CotangentComplex
end CategoryTheory.CommRingCat.Under

namespace Algebra.NaiveCotangent

open CategoryTheory
open CommRingCat.Under.FreeAlgebra
open CommRingCat.Under.CotangentComplex
open DerivedCategory.TStructure

/-- The truncated mapping-cone inclusion of `L_{B/A}` is an isomorphism onto
`τ_{≥ -1} Lπ_!(J/J² ⟶ Ω)`. -/
instance evaluationInr_truncGE_isIso (A : CommRingCat.{u}) (B : Under A) :
    IsIso ((t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationInr A B))) := sorry

/-- The remark-make-map identification `τ_{≥ -1} Lπ_!(J/J² ⟶ Ω) ≅ τ_{≥ -1} L_{B/A}`. -/
def truncGEEvaluationIso (A : CommRingCat.{u}) (B : Under A) :
    (t.truncGE (-1)).obj (DerivedCategory.Q.obj (evaluationCone A B)) ≅
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  (asIso ((t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationInr A B)))).symm

/-- Unfolding of `truncGEEvaluationIso` as the inverse of the truncated mapping-cone
inclusion. -/
theorem truncGEEvaluationIso_eq (A : CommRingCat.{u}) (B : Under A) :
    truncGEEvaluationIso A B =
      (asIso ((t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationInr A B)))).symm := sorry

/-- The canonical morphism in `D(B)` from the two-term naive cotangent complex of a polynomial
arrow `φ : A[E] ⟶ B` to `τ_{≥ -1} L_{B/A}`. -/
def toTruncGE (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    DerivedCategory.Q.obj (naiveComplex A B E φ) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (naiveComplex A B E φ)) ≫
    (t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationToCone A B E φ)) ≫
      (truncGEEvaluationIso A B).hom

/-- `toTruncGE` is the 08Q6 evaluation of `J/J² ⟶ Ω` at `φ`, truncated and transported along
`truncGEEvaluationIso`. -/
theorem toTruncGE_fac (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    toTruncGE A B E φ =
      (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (naiveComplex A B E φ)) ≫
        (t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationToCone A B E φ)) ≫
          (truncGEEvaluationIso A B).hom := sorry

/-- The polynomial arrow `A[σ] ⟶ B` associated to a generating map `σ → B`. -/
def ofGeneratorsHom (A : CommRingCat.{u}) (B : Under A) {σ : Type u}
    (val : σ ⟶ (carrier A).obj B) :
    (functor A).obj σ ⟶ B :=
  ((adjunction A).homEquiv σ B).symm val

/-- `ofGeneratorsHom` is the adjunct of the generating map `σ → B`. -/
theorem ofGeneratorsHom_eq (A : CommRingCat.{u}) (B : Under A) {σ : Type u}
    (val : σ ⟶ (carrier A).obj B) :
    ofGeneratorsHom A B val = ((adjunction A).homEquiv σ B).symm val := sorry

/-- The truncated comparison of a generating map `σ → B`, i.e. of the object
`A[σ] ⟶ B` of `C_{B/A}`. -/
def toTruncGE_ofGenerators (A : CommRingCat.{u}) (B : Under A) {σ : Type u}
    (val : σ ⟶ (carrier A).obj B) :
    DerivedCategory.Q.obj (naiveComplex A B σ (ofGeneratorsHom A B val)) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  toTruncGE A B σ (ofGeneratorsHom A B val)

/-- `toTruncGE_ofGenerators` is `toTruncGE` of `ofGeneratorsHom`. -/
theorem toTruncGE_ofGenerators_eq (A : CommRingCat.{u}) (B : Under A) {σ : Type u}
    (val : σ ⟶ (carrier A).obj B) :
    toTruncGE_ofGenerators A B val =
      toTruncGE A B σ (ofGeneratorsHom A B val) := sorry

/-- The empty generating map `∅ → B`. -/
def emptyGenerators (A : CommRingCat.{u}) (B : Under A) :
    PEmpty.{u + 1} ⟶ (carrier A).obj B :=
  TypeCat.ofHom fun (x : PEmpty.{u + 1}) => (PEmpty.elim x : (carrier A).obj B)

/-- Unfolding of the empty generating map as empty elimination. -/
theorem emptyGenerators_eq (A : CommRingCat.{u}) (B : Under A) :
    emptyGenerators A B =
      TypeCat.ofHom fun (x : PEmpty.{u + 1}) =>
        (PEmpty.elim x : (carrier A).obj B) := sorry

/-- The polynomial arrow `A[∅] ⟶ B` presenting the object `(A ⟶ B)` of `C_{B/A}`. -/
def ofBaseHom (A : CommRingCat.{u}) (B : Under A) :
    (functor A).obj PEmpty.{u + 1} ⟶ B :=
  ((adjunction A).homEquiv PEmpty.{u + 1} B).symm (emptyGenerators A B)

/-- `ofBaseHom` is the adjunct of the empty generating map. -/
theorem ofBaseHom_eq (A : CommRingCat.{u}) (B : Under A) :
    ofBaseHom A B = ((adjunction A).homEquiv PEmpty.{u + 1} B).symm (emptyGenerators A B) := sorry

/-- The truncated comparison of the object `(A ⟶ B)` of `C_{B/A}`. -/
def toTruncGE_ofBase (A : CommRingCat.{u}) (B : Under A) :
    DerivedCategory.Q.obj (naiveComplex A B PEmpty.{u + 1} (ofBaseHom A B)) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  toTruncGE A B PEmpty.{u + 1} (ofBaseHom A B)

/-- `toTruncGE_ofBase` is `toTruncGE` of `ofBaseHom`. -/
theorem toTruncGE_ofBase_eq (A : CommRingCat.{u}) (B : Under A) :
    toTruncGE_ofBase A B = toTruncGE A B PEmpty.{u + 1} (ofBaseHom A B) := sorry

/-- For a surjective ring map, the truncated comparison of `(A ⟶ B)` induces the canonical
isomorphism `I/I² ≅ H^{-1}(L_{B/A})`. -/
theorem toTruncGE_surjection_homology_negOne (A : CommRingCat.{u}) (B : Under A)
    (hsurj : Function.Surjective B.hom.hom) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B.right) (-1)).map
        (toTruncGE_ofBase A B)) := sorry

/-- The truncated comparison attached to the canonical self-presentation `A[B] ⟶ B`. -/
def toTruncGE_self (A : CommRingCat.{u}) (B : Under A) :
    DerivedCategory.Q.obj (naiveComplex A B B.right ((adjunction A).counit.app B)) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  toTruncGE A B B.right ((adjunction A).counit.app B)

/-- `toTruncGE_self` is `toTruncGE` of the free-forgetful counit. -/
theorem toTruncGE_self_eq (A : CommRingCat.{u}) (B : Under A) :
    toTruncGE_self A B =
      toTruncGE A B B.right ((adjunction A).counit.app B) := sorry

end Algebra.NaiveCotangent

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The truncated cotangent comparison of a ring homomorphism, using the self-presentation of
the codomain. -/
abbrev toTruncGE (f : R →+* S) :=
  Algebra.NaiveCotangent.toTruncGE_self (CommRingCat.of R)
    (Under.mk (CommRingCat.ofHom f))

/-- Unfolding of the ring-hom truncated comparison as the self-presentation comparison. -/
theorem toTruncGE_eq (f : R →+* S) :
    toTruncGE f =
      Algebra.NaiveCotangent.toTruncGE_self (CommRingCat.of R)
        (Under.mk (CommRingCat.ofHom f)) := sorry

end RingHom

namespace CommRingCat.Hom

variable {R S : CommRingCat.{u}}

/-- The truncated cotangent comparison of a bundled commutative-ring morphism. -/
abbrev toTruncGE (f : R ⟶ S) :=
  RingHom.toTruncGE f.hom

/-- Unfolding of the bundled truncated comparison as the ring-hom comparison. -/
theorem toTruncGE_eq (f : R ⟶ S) :
    toTruncGE f = RingHom.toTruncGE f.hom := sorry

end CommRingCat.Hom
