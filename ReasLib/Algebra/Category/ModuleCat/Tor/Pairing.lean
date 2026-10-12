/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.CohomologyProduct
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pairings on Tor

This file constructs the pairing on the canonical `A`-module models for
`Tor^R_n(M, A)`.  The chain-level augmentation from the tensor of two degree-zero
single complexes to the single complex on `M ⊗[R] N` is explicit.  Its derived
comparison is then combined with scalar extension and the cohomology product.

@stack 068J
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct TensorProduct

universe u

-- Local instance justification (instance diamond): select the standard derived-category model
-- only for the Tor pairing construction.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModuleCat.Tor.Pairing

section SingleComplex

variable {R : Type u} [CommRing R]

local notation "singleC" =>
  CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "singleD" =>
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The degreewise augmentation from the tensor of two degree-zero single complexes to the
single complex on the ordinary tensor product. -/
@[stacks 068J "degreewise single-complex tensor augmentation"]
noncomputable def singleTensorComponent (M N : ModuleCat R) (j : ℤ) :
    (HomologicalComplex.tensorObj
      (Functor.obj singleC M) (Functor.obj singleC N)).X j ⟶
      (Functor.obj singleC (ModuleCat.of R ((↑M) ⊗[R] ↑N))).X j :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦
    if hp : p = 0 then
      if hq : q = 0 then
        let hj : j = 0 :=
          h.symm.trans ((congrArg₂ (· + ·) hp hq).trans (zero_add 0))
        ((HomologicalComplex.singleObjXIsoOfEq
              (ComplexShape.up ℤ) 0 M p hp).hom ⊗ₘ
            (HomologicalComplex.singleObjXIsoOfEq
              (ComplexShape.up ℤ) 0 N q hq).hom) ≫
          (HomologicalComplex.singleObjXIsoOfEq
            (ComplexShape.up ℤ) 0
            (ModuleCat.of R ((↑M) ⊗[R] ↑N)) j hj).inv
      else 0
    else 0

/-- The degreewise single-complex tensor augmentation commutes with the differentials. -/
@[stacks 068J "single-complex tensor augmentation commutes with differentials"]
theorem singleTensorComponent_comm
    (M N : ModuleCat R) (i j : ℤ) (h : (ComplexShape.up ℤ).Rel i j) :
    singleTensorComponent M N i ≫
        (Functor.obj singleC (ModuleCat.of R ((↑M) ⊗[R] ↑N))).d i j =
      (HomologicalComplex.tensorObj
          (Functor.obj singleC M) (Functor.obj singleC N)).d i j ≫
        singleTensorComponent M N j := sorry

/-- The canonical augmentation from the tensor of two degree-zero single complexes to the
degree-zero single complex on their ordinary tensor product. -/
@[stacks 068J "single-complex tensor augmentation"]
noncomputable def singleTensorComplexMap (M N : ModuleCat R) :
    HomologicalComplex.tensorObj
        (Functor.obj singleC M) (Functor.obj singleC N) ⟶
      Functor.obj singleC (ModuleCat.of R ((↑M) ⊗[R] ↑N)) :=
  HomologicalComplex.Hom.mk (singleTensorComponent M N)
    (singleTensorComponent_comm M N)

/-- The canonical derived tensor augmentation for two modules placed in degree zero. -/
@[stacks 068J "derived single-object tensor augmentation"]
noncomputable def singleTensorComparison (M N : ModuleCat R) :
    DerivedCategory.DerivedTensor.Bifunctor.obj
        (Functor.obj singleD M) (Functor.obj singleD N) ⟶
      Functor.obj singleD (ModuleCat.of R ((↑M) ⊗[R] ↑N)) :=
  let SM := Functor.obj singleC M
  let SN := Functor.obj singleC N
  DerivedCategory.DerivedTensor.Bifunctor.functor.map
      (Prod.mkHom
        ((DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat R) (0 : ℤ)).hom.app M)
        ((DerivedCategory.singleFunctorIsoCompQ
          (ModuleCat R) (0 : ℤ)).hom.app N)) ≫
    DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ SM SN ≫
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)).map (singleTensorComplexMap M N) ≫
    (DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat R) (0 : ℤ)).inv.app
      (ModuleCat.of R ((↑M) ⊗[R] ↑N))

end SingleComplex

section ScalarExtension

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "singleD" =>
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The comparison from the fixed-right derived tensor of two scalar-extended degree-zero
objects to the scalar extension of their ordinary tensor product. -/
@[stacks 068J "scalar-extended tensor target comparison"]
noncomputable def scalarExtensionTensorComparison (M N : ModuleCat R) :
    let E := ModuleCat.DerivedExtension.Tensor.extension (algebraMap R A)
    DerivedCategory.DerivedTensor.Right.obj
        (E.obj (Functor.obj singleD M)) (E.obj (Functor.obj singleD N)) ⟶
      E.obj (Functor.obj singleD (ModuleCat.of R ((↑M) ⊗[R] ↑N))) :=
  let M0 := Functor.obj singleD M
  let N0 := Functor.obj singleD N
  let E := ModuleCat.DerivedExtension.Tensor.extension (algebraMap R A)
  let XM := E.obj M0
  let XN := E.obj N0
  let rightToBifunctor :
      DerivedCategory.DerivedTensor.Right.obj XM XN ⟶
        DerivedCategory.DerivedTensor.Bifunctor.obj XM XN :=
    (DerivedCategory.DerivedTensor.Bifunctor.Right.isoApp XN XM).hom
  let scalarComparison :
      DerivedCategory.DerivedTensor.Bifunctor.obj XM XN ⟶
        E.obj (DerivedCategory.DerivedTensor.Bifunctor.obj M0 N0) :=
    (ModuleCat.DerivedExtension.Tensor.comparisonIsoApp
      (algebraMap R A) M0 N0).inv
  rightToBifunctor ≫ scalarComparison ≫ E.map (singleTensorComparison M N)

end ScalarExtension

section Pairing

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [(DerivedCategory.Qh :
  HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤
    DerivedCategory (ModuleCat A)).Monoidal]

local notation "Hₐ" =>
  DerivedCategory.homologyFunctor (ModuleCat A)
local notation "singleD" =>
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The canonical `A`-module model for `Tor^R_n(M, A)`, obtained as degree `-n` cohomology
after derived extension of scalars. -/
@[stacks 068J "A-module model for Tor"]
noncomputable abbrev obj (M : ModuleCat R) (n : ℕ) : ModuleCat A :=
  (Hₐ (-(n : ℤ))).obj
    ((ModuleCat.DerivedExtension.Tensor.extension
      (algebraMap R A)).obj (Functor.obj singleD M))

/-- Equation 15.64.0.3 (068J): the Tor pairing constructed from an explicit derived tensor
model on `D(A)`. -/
@[stacks 068J "Tor pairing from an explicit derived tensor model"]
noncomputable def pairingOf
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat A))
    (M N : ModuleCat R) (n m : ℕ) :
    (obj (A := A) M n ⊗ obj (A := A) N m : ModuleCat A) ⟶
      obj (A := A) (ModuleCat.of R ((↑M) ⊗[R] ↑N)) (n + m) :=
  let M0 := Functor.obj singleD M
  let N0 := Functor.obj singleD N
  let E := ModuleCat.DerivedExtension.Tensor.extension (algebraMap R A)
  let XM := E.obj M0
  let XN := E.obj N0
  let degreeEq : (-(n : ℤ) + -(m : ℤ)) = -((n + m : ℕ) : ℤ) :=
    (Int.neg_add (a := (n : ℤ)) (b := (m : ℤ))).symm.trans
      (congrArg Neg.neg (Nat.cast_add n m).symm)
  derivedCohomologyProduct T (-(n : ℤ)) (-(m : ℤ)) XM XN ≫
    eqToHom
      (congrArg
        (fun i => (Hₐ i).obj (XM ⊗[A]^L XN)) degreeEq) ≫
    (Hₐ (-((n + m : ℕ) : ℤ))).map
      (scalarExtensionTensorComparison (A := A) M N)

variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [(DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
  DerivedCategory (ModuleCat A)).Monoidal]

/-- Equation 15.64.0.3 (068J): the canonical pairing
`Tor^R_n(M, A) ⊗[A] Tor^R_m(N, A) ⟶ Tor^R_{n+m}(M ⊗[R] N, A)`. -/
@[stacks 068J "canonical Tor pairing"]
noncomputable def pairing (M N : ModuleCat R) (n m : ℕ) :
    (obj (A := A) M n ⊗ obj (A := A) N m : ModuleCat A) ⟶
      obj (A := A) (ModuleCat.of R ((↑M) ⊗[R] ↑N)) (n + m) :=
  pairingOf
    (DerivedCategory.DerivedTensor.Right.Monoidal.Strong.modelFamily
      (C := ModuleCat A)) M N n m

end Pairing

end CategoryTheory.ModuleCat.Tor.Pairing
