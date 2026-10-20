/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Kernel-to-differentials comparison of a polynomial presentation

The two-term `A`-module complex `J ⟶ Ω_{P/A} ⊗_P B` of a polynomial
presentation `φ : A[E] ⟶ B`, the canonical map `P ⟶ P_0` to the standard degree-zero
term, and the evaluation of `𝒥 ⟶ Ω` into the standard-resolution mapping cone that
computes `Lπ_!(𝒥 ⟶ Ω)` in `D(A)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open HomologicalComplex
open AlgebraicTopology
open scoped Simplicial ZeroObject TensorProduct ChangeOfRings

noncomputable section

universe u

namespace CategoryTheory.CommRingCat.Under
namespace CotangentComplex.Comparison

open CommRingCat.Under.FreeAlgebra

/-- The kernel of a polynomial presentation `φ : A[E] ⟶ B`, viewed as an `A`-module. -/
def kernelModule (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars ((functor A).obj E).hom.hom).obj
    (ModuleCat.of ((functor A).obj E).right (RingHom.ker φ.right.hom))

/-- The module `Ω_{P/A} ⊗_P B` of a polynomial presentation, viewed as an `A`-module. -/
def differentialsModule (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars B.hom.hom).obj
    ((ModuleCat.extendScalars φ.right.hom).obj
      (CommRingCat.KaehlerDifferential ((functor A).obj E).hom))

/-- The differential `J ⟶ Ω_{P/A} ⊗_P B` of a polynomial presentation, as an `A`-module map. -/
def kernelToDifferentials (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelModule A B E φ ⟶ differentialsModule A B E φ := by
  let P := (functor A).obj E
  refine ConcreteCategory.ofHom
    { toFun := fun j ↦
        (1 : B.right) ⊗ₜ[P.right, φ.right.hom]
          (CommRingCat.KaehlerDifferential.d (j : RingHom.ker φ.right.hom).1)
      map_add' := ?_
      map_smul' := ?_ }
  all_goals sorry

/-- The two-term chain complex `J ⟶ Ω_{P/A} ⊗_P B` of a polynomial presentation. -/
def kernelDifferentialsChain (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.mk'
    (differentialsModule A B E φ)
    (kernelModule A B E φ)
    (kernelToDifferentials A B E φ)
    (fun {_ _} _ ↦ ⟨0, 0, zero_comp⟩)

/-- The two-term cochain complex `(J ⟶ Ω_{P/A} ⊗_P B)` of a polynomial presentation, placed
in cohomological degrees `-1` and `0`. -/
def kernelDifferentialsComplex (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (kernelDifferentialsChain A B E φ).extend ComplexShape.embeddingDownNat

/-- Identification of the degree-`0` term with `Ω_{P/A} ⊗_P B`. -/
def kernelDifferentialsComplex_X_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (kernelDifferentialsComplex A B E φ).X 0 ≅ differentialsModule A B E φ :=
  extendXIso (kernelDifferentialsChain A B E φ) ComplexShape.embeddingDownNat
    (rfl : ComplexShape.embeddingDownNat.f 0 = 0)

/-- Identification of the degree-`-1` term with the kernel `J`. -/
def kernelDifferentialsComplex_X_negOne (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (kernelDifferentialsComplex A B E φ).X (-1) ≅ kernelModule A B E φ :=
  extendXIso (kernelDifferentialsChain A B E φ) ComplexShape.embeddingDownNat
    (rfl : ComplexShape.embeddingDownNat.f 1 = -1)

/-- The differential in degrees `-1 ⟶ 0` is `kernelToDifferentials`, as an `A`-module map. -/
theorem kernelDifferentialsComplex_d (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (kernelDifferentialsComplex A B E φ).d (-1) 0 =
      (kernelDifferentialsComplex_X_negOne A B E φ).hom ≫
        kernelToDifferentials A B E φ ≫
          (kernelDifferentialsComplex_X_zero A B E φ).inv := sorry

/-- The canonical `A`-algebra map from a polynomial presentation `P = A[E]` to the standard
degree-zero term `P_0`, induced by `E ⟶ |B|` along `φ`. -/
def toStandard (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (functor A).obj E ⟶ standardTerm A B (op ⦋0⦌) :=
  (functor A).map ((adjunction A).homEquiv E B φ)

/-- `L_{B/A}` viewed as a complex of `A`-modules by restriction of scalars. -/
abbrev objRestrictScalars (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.restrictScalars B.hom.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (obj A B)

/-- The map of relative Kähler differentials induced by `toStandard`. -/
def comparisonDifferentialsMap (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    CommRingCat.KaehlerDifferential ((functor A).obj E).hom ⟶
      (ModuleCat.restrictScalars (toStandard A B E φ).right.hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B (op ⦋0⦌)).hom) :=
  CommRingCat.KaehlerDifferential.map
    ((Category.id_comp (standardTerm A B (op ⦋0⦌)).hom).trans (toStandard A B E φ).w.symm)

/-- The polynomial presentation `φ` is recovered by composing `toStandard` with the
standard-resolution augmentation. -/
theorem toStandard_comp_augmentation_hom (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    φ.right.hom =
      (standardAugmentation A B (op ⦋0⦌)).hom.comp (toStandard A B E φ).right.hom := sorry

/-- Degree-`0` component of the comparison, as a map `Ω_{P/A} ⊗_P B ⟶ Ω_{P_0/A} ⊗_{P_0} B`
of `A`-modules. -/
def comparison_f_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    differentialsModule A B E φ ⟶
      (ModuleCat.restrictScalars B.hom.hom).obj ((simplicialModule A B).obj (op ⦋0⦌)) :=
  (ModuleCat.restrictScalars B.hom.hom).map
    (((ModuleCat.extendRestrictScalarsAdj φ.right.hom).homEquiv _ _).symm
      (comparisonDifferentialsMap A B E φ ≫
        (ModuleCat.restrictScalars (toStandard A B E φ).right.hom).map
          ((ModuleCat.extendRestrictScalarsAdj
              (standardAugmentation A B (op ⦋0⦌)).hom).unit.app _) ≫
        (ModuleCat.restrictScalarsComp'
          (toStandard A B E φ).right.hom
          (standardAugmentation A B (op ⦋0⦌)).hom
          φ.right.hom
          (toStandard_comp_augmentation_hom A B E φ)).inv.app _))

/-- The kernel of the standard-resolution augmentation `P_n ⟶ B`, as an `A`-module. -/
def standardKernelModule (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (standardTerm A B n).hom.hom).obj
    (ModuleCat.of (standardTerm A B n).right
      (RingHom.ker (standardAugmentation A B n).hom))

/-- Unfolding of `standardKernelModule` as restriction of scalars of the kernel of the
standard-resolution augmentation. -/
theorem standardKernelModule_eq (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    standardKernelModule A B n =
      (ModuleCat.restrictScalars (standardTerm A B n).hom.hom).obj
        (ModuleCat.of (standardTerm A B n).right
          (RingHom.ker (standardAugmentation A B n).hom)) := sorry

/-- The `A`-module map on kernels induced by a simplicial operator of the polynomial
resolution. -/
def standardKernelMap (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    standardKernelModule A B n ⟶ standardKernelModule A B m := by
  refine ConcreteCategory.ofHom
    { toFun := fun j ↦
        ⟨(standardMap A B φ).right (j : RingHom.ker (standardAugmentation A B n).hom).1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  all_goals sorry

/-- The simplicial `A`-module of kernels `Ker(P_n ⟶ B)` of the standard polynomial resolution. -/
def kernelSimplicial (A : CommRingCat.{u}) (B : Under A) :
    SimplicialObject (ModuleCat.{u} A) := by
  refine
    { obj n := standardKernelModule A B n
      map φ := standardKernelMap A B φ
      map_id n := ?_
      map_comp φ ψ := ?_ }
  all_goals sorry

/-- Degreewise, `kernelSimplicial` is the kernel of the corresponding standard-resolution
augmentation. -/
theorem kernelSimplicial_obj (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (kernelSimplicial A B).obj n = standardKernelModule A B n := sorry

/-- The differential `Ker(P_n ⟶ B) ⟶ Ω_{P_n/A} ⊗_{P_n} B` of a standard-resolution term, as an
`A`-module map. -/
def standardKernelToDifferentials (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    standardKernelModule A B n ⟶
      (ModuleCat.restrictScalars B.hom.hom).obj ((simplicialModule A B).obj n) := by
  refine ConcreteCategory.ofHom
    { toFun := fun j ↦
        (1 : B.right) ⊗ₜ[(standardTerm A B n).right, (standardAugmentation A B n).hom]
          (CommRingCat.KaehlerDifferential.d
            (j : RingHom.ker (standardAugmentation A B n).hom).1)
      map_add' := ?_
      map_smul' := ?_ }
  all_goals sorry

/-- The simplicial map `𝒥(P_•) ⟶ Ω(P_•)` on the standard polynomial resolution, as `A`-modules. -/
def kernelSimplicialToOmega (A : CommRingCat.{u}) (B : Under A) :
    kernelSimplicial A B ⟶
      simplicialModule A B ⋙ ModuleCat.restrictScalars B.hom.hom where
  app n := standardKernelToDifferentials A B n
  naturality _ _ _ := sorry

/-- The alternating-face chain complex of `Ker(P_n ⟶ B)`. -/
def standardKernelChain (A : CommRingCat.{u}) (B : Under A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (kernelSimplicial A B)

/-- The cochain complex of `A`-modules associated to `Ker(P_n ⟶ B)`, placed in nonpositive
cohomological degrees. -/
def standardKernelComplex (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (standardKernelChain A B).extend ComplexShape.embeddingDownNat

/-- Identification of the cohomological degree `-n` term of `standardKernelComplex` with
`Ker(P_n ⟶ B)`. -/
def standardKernelComplex_X (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (standardKernelComplex A B).X (-n) ≅ standardKernelModule A B (op ⦋n⦌) :=
  extendXIso (standardKernelChain A B) ComplexShape.embeddingDownNat
    (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- Components of the cochain map `Ker(P_• ⟶ B) ⟶ L_{B/A}` after restriction of scalars to `A`. -/
def standardKernelToOmega_f (A : CommRingCat.{u}) (B : Under A) :
    ∀ i : ℤ, (standardKernelComplex A B).X i ⟶ (objRestrictScalars A B).X i
  | Int.ofNat 0 =>
      (standardKernelComplex_X A B 0).hom ≫
        standardKernelToDifferentials A B (op ⦋0⦌) ≫
          (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B 0).inv
  | Int.negSucc n =>
      (standardKernelComplex_X A B (n + 1)).hom ≫
        standardKernelToDifferentials A B (op ⦋n + 1⦌) ≫
          (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B (n + 1)).inv
  | Int.ofNat (_n + 1) => 0

/-- The cochain map `Ker(P_• ⟶ B) ⟶ L_{B/A}` of `A`-modules induced by `j ↦ 1 ⊗ d(j)` on each
standard-resolution term. -/
def standardKernelToOmega (A : CommRingCat.{u}) (B : Under A) :
    standardKernelComplex A B ⟶ objRestrictScalars A B where
  f := standardKernelToOmega_f A B
  comm' := sorry

/-- Degree `0` of `standardKernelToOmega` is `1 ⊗ d` on `Ker(P_0 ⟶ B)`. -/
theorem standardKernelToOmega_f_zero (A : CommRingCat.{u}) (B : Under A) :
    (standardKernelToOmega A B).f 0 =
      (standardKernelComplex_X A B 0).hom ≫
        standardKernelToDifferentials A B (op ⦋0⦌) ≫
          (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B 0).inv := sorry

/-- The homotopy cofiber of `standardKernelToOmega` exists by biproducts in `ModuleCat`. -/
instance hasHomotopyCofiber_standardKernelToOmega (A : CommRingCat.{u}) (B : Under A) :
    HasHomotopyCofiber (standardKernelToOmega A B) := inferInstance

/-- The mapping cone of `𝒥(P_•) ⟶ Ω(P_•)`, computing `Lπ_!(𝒥 ⟶ Ω)` on the standard polynomial
resolution. -/
def standardEvaluationCone (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.mappingCone (standardKernelToOmega A B)

/-- Unfolding of `standardEvaluationCone` as the mapping cone of `standardKernelToOmega`. -/
theorem standardEvaluationCone_eq (A : CommRingCat.{u}) (B : Under A) :
    standardEvaluationCone A B =
      CochainComplex.mappingCone (standardKernelToOmega A B) := sorry

/-- The inclusion of `L_{B/A}` into the mapping cone of `𝒥(P_•) ⟶ Ω(P_•)`. -/
def omegaInr (A : CommRingCat.{u}) (B : Under A) :
    objRestrictScalars A B ⟶ standardEvaluationCone A B :=
  CochainComplex.mappingCone.inr (standardKernelToOmega A B)

/-- `omegaInr` is the mapping-cone inclusion of the `Ω` rows. -/
theorem omegaInr_eq (A : CommRingCat.{u}) (B : Under A) :
    omegaInr A B = CochainComplex.mappingCone.inr (standardKernelToOmega A B) := sorry

/-- The map on kernels induced by `toStandard : P ⟶ P_0`. -/
def kernelToStandard (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelModule A B E φ ⟶ standardKernelModule A B (op ⦋0⦌) := by
  refine ConcreteCategory.ofHom
    { toFun := fun j ↦
        ⟨(toStandard A B E φ).right (j : RingHom.ker φ.right.hom).1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  all_goals sorry

/-- `toStandard` sends `Ker(φ)` into `Ker(P_0 ⟶ B)`. -/
theorem toStandard_mem_ker (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) (j : RingHom.ker φ.right.hom) :
    (standardAugmentation A B (op ⦋0⦌)).hom ((toStandard A B E φ).right j.1) = 0 := sorry

/-- Naturality of `1 ⊗ d` along `toStandard`. -/
theorem kernelToStandard_comp_standardKernelToDifferentials
    (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelToStandard A B E φ ≫ standardKernelToDifferentials A B (op ⦋0⦌) =
      kernelToDifferentials A B E φ ≫ comparison_f_zero A B E φ := sorry

/-- The relation `ComplexShape.up ℤ` used to include the degree-zero kernel into the mapping
cone in cohomological degree `-1`. -/
theorem up_rel_negOne_zero : ComplexShape.Rel (ComplexShape.up ℤ) (-1) 0 := rfl

/-- Components of the evaluation map from a polynomial presentation into the standard-resolution
mapping cone of `𝒥 ⟶ Ω`. -/
def evaluationToMappingCone_f (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    ∀ i : ℤ,
      (kernelDifferentialsComplex A B E φ).X i ⟶ (standardEvaluationCone A B).X i :=
  fun i ↦
    if h0 : i = 0 then
      eqToHom (congrArg (kernelDifferentialsComplex A B E φ).X h0) ≫
        (kernelDifferentialsComplex_X_zero A B E φ).hom ≫
          comparison_f_zero A B E φ ≫
            (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B 0).inv ≫
              (omegaInr A B).f 0 ≫
                eqToHom (congrArg (standardEvaluationCone A B).X h0.symm)
    else if h1 : i = -1 then
      eqToHom (congrArg (kernelDifferentialsComplex A B E φ).X h1) ≫
        (kernelDifferentialsComplex_X_negOne A B E φ).hom ≫
          kernelToStandard A B E φ ≫
            (standardKernelComplex_X A B 0).inv ≫
              HomologicalComplex.homotopyCofiber.inlX (standardKernelToOmega A B) 0 (-1)
                up_rel_negOne_zero ≫
                eqToHom (congrArg (standardEvaluationCone A B).X h1.symm)
    else
      0

/-- The cochain map evaluating `𝒥 ⟶ Ω` at a polynomial presentation `φ` and sending the result
to the standard-resolution computation of `Lπ_!(𝒥 ⟶ Ω)`. Degree `0` is the map of Kähler
differentials along `toStandard`; degree `-1` is the induced map on kernels `J ⟶ Ker(P_0 ⟶ B)`. -/
def evaluationToMappingCone (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    kernelDifferentialsComplex A B E φ ⟶ standardEvaluationCone A B where
  f := evaluationToMappingCone_f A B E φ
  comm' := sorry

/-- Degree `0` of `evaluationToMappingCone` is `comparison_f_zero` followed by `omegaInr`. -/
theorem evaluationToMappingCone_f_zero (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    (evaluationToMappingCone A B E φ).f 0 =
      (kernelDifferentialsComplex_X_zero A B E φ).hom ≫
        comparison_f_zero A B E φ ≫
          (ModuleCat.restrictScalars B.hom.hom).map (objXIso A B 0).inv ≫
            (omegaInr A B).f 0 := sorry


/-- The inclusion of `L_{B/A}` into the standard-resolution mapping cone of `𝒥 ⟶ Ω` is a
quasi-isomorphism, since `Lπ_!(𝒥) = 0`. -/
instance omegaInr_quasiIso (A : CommRingCat.{u}) (B : Under A) :
    QuasiIso (omegaInr A B) := sorry

/-- Quasi-isomorphisms become isomorphisms in the derived category. -/
instance omegaInr_isIso (A : CommRingCat.{u}) (B : Under A) :
    IsIso (DerivedCategory.Q.map (omegaInr A B)) := inferInstance

/-- The canonical derived morphism from the kernel-to-differentials complex of a polynomial
presentation to the cotangent complex, obtained by evaluation and the inverse of the
standard mapping-cone inclusion. -/
def comparisonDerived (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    DerivedCategory.Q.obj (kernelDifferentialsComplex A B E φ) ⟶
      DerivedCategory.Q.obj (objRestrictScalars A B) :=
  DerivedCategory.Q.map (evaluationToMappingCone A B E φ) ≫
    (asIso (DerivedCategory.Q.map (omegaInr A B))).inv

/-- The derived comparison factors as evaluation into the standard mapping cone followed
by the inverse of the cotangent-complex inclusion. -/
theorem comparisonDerived_fac (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    comparisonDerived A B E φ =
      DerivedCategory.Q.map (evaluationToMappingCone A B E φ) ≫
        (asIso (DerivedCategory.Q.map (omegaInr A B))).inv := sorry

end CotangentComplex.Comparison
end CategoryTheory.CommRingCat.Under
