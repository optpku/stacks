/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_11_1_2_Comparison»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Truncated comparison from a presentationwise naive cotangent complex

This leaf records the source-facing truncated comparison of Stacks 08R9, reusing the
polynomial-arrow morphism `Algebra.NaiveCotangent.toTruncGE`.
-/

@[expose] public section

open CategoryTheory
open CommRingCat.Under.FreeAlgebra
open CommRingCat.Under.CotangentComplex
open Algebra.NaiveCotangent
open DerivedCategory.TStructure

universe u

noncomputable section

namespace Algebra.NaiveCotangent

/-- 92.11.1.2: let `A ⟶ B` be a ring map. For any object `U = (P ⟶ B)` of `C_{B/A}`,
writing `J = Ker(P ⟶ B)`, there is a canonical morphism
`(J/J² ⟶ Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}` in `D(B)`, obtained by evaluating the
two-term complex `J/J² ⟶ Ω` at `U` and using
`τ_{≥ -1} Lπ_!(J/J² ⟶ Ω) = τ_{≥ -1} L_{B/A}`. -/
@[stacks 08R9]
def naiveCotangentToTruncGE (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    DerivedCategory.Q.obj (naiveComplex A B E φ) ⟶
      (t.truncGE (-1)).obj (DerivedCategory.Q.obj (obj A B)) :=
  (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (naiveComplex A B E φ)) ≫
    (t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationToCone A B E φ)) ≫
      (truncGEEvaluationIso A B).hom

/-- The labeled comparison is the 08Q6 evaluation of `J/J² ⟶ Ω` at the polynomial arrow
`φ : A[E] ⟶ B`, truncated and transported along `truncGEEvaluationIso`. -/
theorem naiveCotangentToTruncGE_fac (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    naiveCotangentToTruncGE A B E φ =
      (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (naiveComplex A B E φ)) ≫
        (t.truncGE (-1)).map (DerivedCategory.Q.map (evaluationToCone A B E φ)) ≫
          (truncGEEvaluationIso A B).hom := sorry

end Algebra.NaiveCotangent
