/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Int.Interval
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Iterated.Finite
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.Source

/-!
# Dualizability of bounded finite-projective module complexes

A bounded complex of finite-projective modules is dualizable in the closed monoidal category of
cochain complexes.  The dual object, comparison maps, evaluation, coevaluation, and exact pairing
remain owned by the generic `MonoidalClosed.Dual` API. This file constructs the finite sum of
termwise coevaluations and an explicit inverse of the tensor-to-endomorphism comparison, thereby
supplying the finite-projective criterion needed to activate that API.

@stack 0658
@stack 0FNK
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [CommRing R]

/-- A bounded complex with finite-projective terms is a bounded finite-projective complex. -/
@[stacks 0658 "bounded termwise finite-projective complex"]
theorem of_bounded
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : CochainComplex.bounded (ModuleCat R) M)
    (hfp : ∀ n : ℤ, Module.FiniteProjective R (M.X n)) :
    M.IsBoundedFiniteProjective := by
  rcases hM with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine { bounded := ⟨a, b, ha, hb⟩
           finite := ?_
           projective := ?_ }
  · intro n
    exact (hfp n).1
  · intro n
    exact (hfp n).2

/-- Place a functional on `M.X p` in degree `-p` of the existing closed-monoidal dual.
The only nonzero homogeneous component has target degree zero of the tensor unit. -/
noncomputable def dualTerm
    (M : CochainComplex (ModuleCat R) ℤ) (p : ℤ) (φ : M.X p →ₗ[R] R) :
    (MonoidalClosed.dual M).X (-p) :=
  let U := 𝟙_ (CochainComplex (ModuleCat R) ℤ)
  let φ₀ : M.X p ⟶ U.X 0 :=
    ModuleCat.ofHom φ ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (𝟙_ (ModuleCat R))).inv
  ((CategoryTheory.CochainComplex.InternalHom.moduleComplexIso M U).inv.f (-p)).hom
    (Cochain.single φ₀ (-p))

/-- A finite retraction gives the termwise identity tensor. The retraction equation is only
needed for its laws, not to form the tensor; no basis of `M.X p` is assumed. -/
noncomputable def termCoevaluationOfSplit
    (M : CochainComplex (ModuleCat R) ℤ) (p : ℤ) {n : ℕ}
    (f : (Fin n → R) →ₗ[R] M.X p) (g : M.X p →ₗ[R] (Fin n → R)) :
    (M.X p ⊗ (MonoidalClosed.dual M).X (-p) : ModuleCat R) :=
  ∑ j : Fin n, TensorProduct.tmul R (f (Pi.single j 1))
    (dualTerm M p ((LinearMap.proj j).comp g))

/-- The identity tensor of a finite-projective term, obtained from mathlib's proved finite
free retraction theorem. Its value is independent of the selected retraction. -/
noncomputable def termCoevaluation
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] (p : ℤ) :
    (M.X p ⊗ (MonoidalClosed.dual M).X (-p) : ModuleCat R) :=
  let h := Module.Finite.exists_comp_eq_id_of_projective R (M.X p)
  termCoevaluationOfSplit M p h.choose_spec.choose h.choose_spec.choose_spec.choose

/-- Retractions of finite free modules yield the same identity tensor. In particular, the
construction applies to finite-projective modules of varying rank over arbitrary rings. -/
theorem termCoevaluationOfSplit_eq
    (M : CochainComplex (ModuleCat R) ℤ) (p : ℤ) {n m : ℕ}
    (f : (Fin n → R) →ₗ[R] M.X p) (g : M.X p →ₗ[R] (Fin n → R))
    (f' : (Fin m → R) →ₗ[R] M.X p) (g' : M.X p →ₗ[R] (Fin m → R))
    (h : f.comp g = LinearMap.id) (h' : f'.comp g' = LinearMap.id) :
    termCoevaluationOfSplit M p f g = termCoevaluationOfSplit M p f' g' := sorry

/-- Sum the termwise identity tensors in a specified finite degree interval. The summand
inclusions are the native inclusions into the tensor totalization. -/
noncomputable def coevaluationElementIn
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] (a b : ℤ) :
    (M ⊗ MonoidalClosed.dual M).X 0 :=
  ∑ p ∈ Finset.Icc a b,
    (HomologicalComplex.ιTensorObj M (MonoidalClosed.dual M)
      p (-p) 0 (add_neg_cancel p)).hom (termCoevaluation M p)

/-- The finite coevaluation sum, using the strict termwise support bounds in the supplied
bounded finite-projective witness. Empty intervals and zero terms contribute zero. -/
noncomputable def coevaluationElement
    (M : CochainComplex (ModuleCat R) ℤ) [hM : M.IsBoundedFiniteProjective] :
    (M ⊗ MonoidalClosed.dual M).X 0 :=
  coevaluationElementIn M hM.bounded.choose hM.bounded.choose_spec.choose

/-- Any strict support interval computes the same finite coevaluation sum. -/
theorem coevaluationElement_eq_of_bounds
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective]
    (a b : ℤ) (ha : M.IsStrictlyGE a) (hb : M.IsStrictlyLE b) :
    coevaluationElement M = coevaluationElementIn M a b := sorry

/-- The linear map from the module tensor unit determined by the finite coevaluation element. -/
noncomputable def coevaluationZero
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    𝟙_ (ModuleCat R) ⟶ (M ⊗ MonoidalClosed.dual M).X 0 :=
  ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight (coevaluationElement M))

/-- The finite identity-tensor sum is a cycle. The dual differential is the signed transpose;
its contribution cancels the differential on the first tensor factor. -/
theorem coevaluationZero_comp_d
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective]
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    coevaluationZero M ≫ (M ⊗ MonoidalClosed.dual M).d 0 k = 0 := sorry

/-- The actual coevaluation map formed from finite-projective module splittings and finite
degree support. The object and its differential are those of the generic closed dual. -/
noncomputable def finiteProjectiveCoevaluation
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ M ⊗ MonoidalClosed.dual M :=
  HomologicalComplex.mkHomFromSingle (coevaluationZero M) (coevaluationZero_comp_d M)

/-- Reverse the tensor-to-endomorphism comparison by letting the endomorphism act on the
first factor of the explicitly constructed coevaluation. This definition needs no `IsIso`. -/
noncomputable def tensorIhomUnitToEndInverse
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    (ihom M).obj M ⟶ M ⊗ MonoidalClosed.dual M :=
  (ρ_ ((ihom M).obj M)).inv ≫
    ((ihom M).obj M) ◁ finiteProjectiveCoevaluation M ≫
      (α_ ((ihom M).obj M) M (MonoidalClosed.dual M)).inv ≫
        ((β_ ((ihom M).obj M) M).hom ≫ (ihom.ev M).app M) ▷ MonoidalClosed.dual M

/-- The explicit reverse map is a left inverse of the canonical comparison. -/
theorem tensorIhomUnitToEnd_comp_inverse
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    MonoidalClosed.tensorIhomUnitToEnd M ≫ tensorIhomUnitToEndInverse M =
      𝟙 (M ⊗ MonoidalClosed.dual M) := sorry

/-- The explicit reverse map is a right inverse of the canonical comparison. -/
theorem inverse_comp_tensorIhomUnitToEnd
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    tensorIhomUnitToEndInverse M ≫ MonoidalClosed.tensorIhomUnitToEnd M =
      𝟙 ((ihom M).obj M) := sorry

/-- A bounded finite-projective module complex has invertible canonical
tensor-to-endomorphism comparison. -/
@[stacks 0FNK "dualizability of a bounded finite-projective complex", instance]
theorem isIso_tensorIhomUnitToEnd
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    IsIso (MonoidalClosed.tensorIhomUnitToEnd M) :=
  ⟨tensorIhomUnitToEndInverse M,
    tensorIhomUnitToEnd_comp_inverse M, inverse_comp_tensorIhomUnitToEnd M⟩

/-- A bounded finite-projective module complex is right-dualizable. -/
@[stacks 0FNK "dualizability of a bounded finite-projective complex"]
theorem isRightDualizable
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    IsRightDualizable M := by
  let concreteIsIso : IsIso (MonoidalClosed.tensorIhomUnitToEnd M) :=
    isIso_tensorIhomUnitToEnd M
  letI : IsIso (MonoidalClosed.tensorIhomUnitToEnd M) := concreteIsIso
  exact CategoryTheory.IsRightDualizable.of_exactPairing
    (MonoidalClosed.Dual.exactPairing M)

/-- A bounded finite-projective complex is canonically paired, in source order, with its
closed-monoidal dual. -/
@[stacks 0FNK "canonical dual pairing of a bounded finite-projective complex",
  implicit_reducible]
noncomputable def exactPairing
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    ExactPairing M (MonoidalClosed.dual M) :=
  MonoidalClosed.Dual.exactPairing M

/-- The existing generic pairing uses the finite-projective coevaluation constructed here. -/
theorem exactPairing_coevaluation
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    (exactPairing M).coevaluation' = finiteProjectiveCoevaluation M := sorry

/-- An explicit bounded finite-projective witness produces the canonical dual pairing without
installing that witness as a local instance. -/
@[stacks 0FNK "explicit witness for the canonical dual pairing", implicit_reducible]
noncomputable def exactPairingOf
    (M : CochainComplex (ModuleCat R) ℤ) (hM : M.IsBoundedFiniteProjective) :
    ExactPairing M (MonoidalClosed.dual M) :=
  @exactPairing R _ M hM

end CochainComplex.IsBoundedFiniteProjective
