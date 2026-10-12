/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral parts of fractional ideals

The integral part of a fractional ideal is its contraction along the scalar map.  Keeping the
ambient algebra explicit makes this construction independent of a chosen model of the fraction
field.

@stack 031T
-/

@[expose] public section

universe u v

namespace FractionalIdeal

variable {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K]
variable {S : Submonoid R}

/-- The contraction to `R` of a fractional ideal in an `R`-algebra. -/
@[stacks 031T "integral part of a fractional ideal"]
def integralPart (I : FractionalIdeal S K) : Ideal R :=
  (I : Submodule R K).comap (Algebra.linearMap R K)

/-- Membership in the integral part is membership after applying the scalar map. -/
@[simp, stacks 031T "membership in the integral part"]
theorem mem_integralPart {I : FractionalIdeal S K} {r : R} :
    r ∈ I.integralPart ↔ algebraMap R K r ∈ I :=
  Iff.rfl

/-- Contraction of fractional ideals is monotone. -/
@[stacks 031T "monotonicity of the integral part"]
theorem integralPart_mono {I J : FractionalIdeal S K} (h : I ≤ J) :
    I.integralPart ≤ J.integralPart :=
  Submodule.comap_mono h

/-- The integral part of a principal fractional ideal is the contraction of its span. -/
@[simp, stacks 031T "contraction of a principal fractional ideal"]
theorem integralPart_spanSingleton [IsLocalization S K] (x : K) :
    (spanSingleton S x).integralPart =
      (Submodule.span R {x}).comap (Algebra.linearMap R K) := by
  rw [integralPart, coe_spanSingleton]

/-- Membership in the integral part of a principal fractional ideal. -/
@[simp, stacks 031T "integral part of a principal fractional ideal"]
theorem mem_integralPart_spanSingleton [IsLocalization S K] {x : K} {r : R} :
    r ∈ (spanSingleton S x).integralPart ↔ ∃ a : R, a • x = algebraMap R K r := by
  rw [mem_integralPart, mem_spanSingleton]

end FractionalIdeal
