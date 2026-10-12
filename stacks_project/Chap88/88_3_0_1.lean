/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.«88_3_0_1_NaiveCotangent»

@[expose] public section

open Algebra.NaiveCotangent.Adic
open CategoryTheory

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

/-- 88.3.0.1: For a presentation `B = A[x_ι]^∧ / J`, the completed naive
cotangent complex `NL_{B/A}^∧` is the two-term complex
`(J / J² ⟶ ⊕ᵢ B dx_i)` in homological degrees `1` and `0`, with differential
sending the residue of `g ∈ J` to the Jacobian of power-series partials
`fun i ↦ ∂g / ∂x_i`. -/
@[stacks 0AJR]
noncomputable abbrev naiveCotangent (I : Ideal A) (P : Presentation A B I ι) :
    ChainComplex (ModuleCat B) ℕ :=
  complex P

/-- The differential of `NL_{B/A}^∧` in degrees `1 → 0` is the Jacobian of the
completed presentation. -/
theorem naiveCotangent_d_one_zero (I : Ideal A) (P : Presentation A B I ι) :
    (naiveCotangent I P).d 1 0 = ModuleCat.ofHom (jacobian P) := sorry

end Algebra.NaiveCotangent.Adic
