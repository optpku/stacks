/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Remark_92_11_4_Comparison
public import stacks_project.Chap92.Lemma_92_11_3
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit comparison map from `L_{B/A}` to the naive cotangent complex

Remark 92.11.4 makes the comparison of Lemma 92.11.3 explicit as a map of
complexes `L_{B/A} ⟶ NL_{B/A}`, with identity on `Ω_{P₀/A} ⊗_{P₀} B` and with
the face-difference rule on `Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`.
-/

@[expose] public section

open CategoryTheory
open Algebra.NaiveCotangent
open CommRingCat.Under
open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra
open DerivedCategory.TStructure

universe u

noncomputable section

namespace Algebra.NaiveCotangent

/-- Remark 92.11.4 (1). The comparison map of Lemma 92.11.3 is made explicit as the cochain
map `L_{B/A} ⟶ NL_{B/A}` of the standard resolution `P_•` of `B` over `A`, with
`P₀ = A[B]` and `I = Ker(A[B] ⟶ B)`: the degree-`0` identification of
`Ω_{P₀/A} ⊗_{P₀} B`, the face-difference rule sending `d f ⊗ b` to the class of
`(d₀ f - d₁ f) b` in `I/I²`, and `0` in degrees `≤ -2`. -/
@[stacks 08UP]
def toNaive (A : CommRingCat.{u}) (B : Under A) :
    obj A B ⟶ selfNaiveComplex A B :=
  CotangentComplex.toNaive A B

/-- Unfolding of the source-facing `toNaive` as the cochain-map owner. -/
theorem toNaive_eq (A : CommRingCat.{u}) (B : Under A) :
    toNaive A B = CotangentComplex.toNaive A B := sorry

/-- Remark 92.11.4 (2). After `τ_{≥ -1}` and the derived-category functor `Q`, the
explicit cochain map `toNaive` is the inverse of `toTruncGE_self`. -/
@[stacks 08UP]
theorem toNaive_inv_toTruncGE_self (A : CommRingCat.{u}) (B : Under A) :
    (t.truncGE (-1)).map (DerivedCategory.Q.map (toNaive A B)) =
      inv (toTruncGE_self A B) ≫
        (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (selfNaiveComplex A B)) :=
  sorry

end Algebra.NaiveCotangent
