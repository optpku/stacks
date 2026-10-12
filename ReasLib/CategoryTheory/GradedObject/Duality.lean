/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.KoszulBraiding
public import ReasLib.CategoryTheory.Monoidal.Duality.Module
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Duality of graded vector spaces

This file exposes the degreewise exact pairings cut out by an exact pairing of graded vector
spaces.  It separates the concrete projection and evaluation maps from the finite-support and
nondegeneracy theorems.
-/

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.GradedObject

open CategoryTheory Limits MonoidalCategory
open GradedObject.Monoidal

variable {F : Type u} [Field F]

/-- A graded vector space has finite total dimension when every graded piece is finite
dimensional and its finite-rank support is finite. -/
def FiniteTotalDimension {I : Type*} (V : GradedObject I (ModuleCat F)) : Prop :=
  Set.Finite (_root_.GradedObject.finrankSupport V) ∧ ∀ i, FiniteDimensional F (V i)

/-- For graded vector spaces, finite total dimension can equivalently be expressed using the set
of nonzero graded pieces. -/
theorem finiteTotalDimension_iff {I : Type*} (V : GradedObject I (ModuleCat F)) :
    FiniteTotalDimension V ↔
      Set.Finite {i : I | ¬ IsZero (V i)} ∧ ∀ i, FiniteDimensional F (V i) := sorry

namespace ExactPairing

variable {V W : GradedObject ℤ (ModuleCat F)}

/-- Projection from degree zero of a graded tensor product onto a selected homogeneous
summand. -/
noncomputable def tensorProjection
    (V W : GradedObject ℤ (ModuleCat F)) (a b : ℤ) :
    (V ⊗ W) 0 ⟶ V a ⊗ W b :=
  tensorObjDesc fun p q _ ↦
    if h : p = a ∧ q = b then
      eqToHom (congrArg₂ (fun i j ↦ V i ⊗ W j) h.1 h.2)
    else 0

/-- The selected homogeneous summand is fixed by its tensor projection. -/
@[reassoc]
theorem ι_tensorProjection (V W : GradedObject ℤ (ModuleCat F))
    (a b : ℤ) (h : a + b = 0) :
    ιTensorObj V W a b 0 h ≫ tensorProjection V W a b = 𝟙 (V a ⊗ W b) := sorry

/-- A tensor projection vanishes on every other homogeneous summand. -/
@[reassoc]
theorem ι_tensorProjection_eq_zero (V W : GradedObject ℤ (ModuleCat F))
    (a b p q : ℤ) (h : p + q = 0) (h_ne : ¬ (p = a ∧ q = b)) :
    ιTensorObj V W p q 0 h ≫ tensorProjection V W a b = 0 := sorry

/-- The degreewise coevaluation obtained by projecting the degree-zero global coevaluation. -/
noncomputable def degreewiseCoevaluationHom (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    𝟙_ (ModuleCat F) ⟶ W (-n) ⊗ V n :=
  tensorUnit₀.inv ≫ p.coevaluation' 0 ≫ tensorProjection W V (-n) n

/-- The degreewise evaluation in exact-pairing order `V n ⊗ W (-n)`. -/
def rawDegreewiseEvaluationHom (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    V n ⊗ W (-n) ⟶ 𝟙_ (ModuleCat F) :=
  ιTensorObj V W n (-n) 0 (add_neg_cancel n) ≫ p.evaluation' 0 ≫ tensorUnit₀.hom

/-- The projected coevaluation and evaluation form an exact pairing on every degree. -/
@[implicit_reducible]
noncomputable def degreewise (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    CategoryTheory.ExactPairing (W (-n)) (V n) where
  coevaluation' := degreewiseCoevaluationHom p n
  evaluation' := rawDegreewiseEvaluationHom p n
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- The coevaluation of the projected exact pairing is the degreewise coevaluation map. -/
theorem degreewise_coevaluation' (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    (degreewise p n).coevaluation' = degreewiseCoevaluationHom p n := sorry

/-- The evaluation of the projected exact pairing is the raw degreewise evaluation map. -/
theorem degreewise_evaluation' (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    (degreewise p n).evaluation' = rawDegreewiseEvaluationHom p n := sorry

/-- The degreewise evaluation written in the textbook order `W (-n) ⊗ V n`, using the
Koszul-signed swap. -/
def degreewiseEvaluationHom (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    W (-n) ⊗ V n ⟶ 𝟙_ (ModuleCat F) :=
  ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫
    koszulBraidingHom W V 0 ≫ p.evaluation' 0 ≫ tensorUnit₀.hom

/-- The curried degreewise evaluation in the order `W (-n) → V n → F`. -/
def degreewiseEvaluation (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    W (-n) →ₗ[F] V n →ₗ[F] F :=
  TensorProduct.curry (degreewiseEvaluationHom p n).hom

/-- The right member of an exact pairing of graded vector spaces has finite total dimension. -/
@[stacks 0FFV]
theorem right_finiteTotalDimension (p : CategoryTheory.ExactPairing W V) :
    FiniteTotalDimension V := sorry

/-- The left member of an exact pairing of graded vector spaces has finite total dimension. -/
theorem left_finiteTotalDimension (p : CategoryTheory.ExactPairing W V) :
    FiniteTotalDimension W := sorry

/-- Every degreewise evaluation induced by an exact pairing of graded vector spaces is
nondegenerate. -/
theorem degreewiseEvaluation_nondegenerate
    (p : CategoryTheory.ExactPairing W V) (n : ℤ) :
    (degreewiseEvaluation p n).Nondegenerate := sorry

end ExactPairing

end CategoryTheory.GradedObject
