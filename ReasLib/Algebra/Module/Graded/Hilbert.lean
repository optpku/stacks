/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.LocallyFinite
public import ReasLib.Algebra.Module.Graded.Basic
public import ReasLib.Algebra.Module.EulerPoincare
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Polynomial.Numerical

/-!
# Hilbert functions of locally finite graded modules

The Hilbert function evaluates an Euler-Poincaré function on each degree piece. Having a Hilbert
polynomial means that these values eventually agree with a numerical polynomial.
-/

@[expose] public section

universe u v

namespace GradedModule

open Module.EulerPoincareFunction

/-- The Hilbert function of a locally finite ℤ-graded module is `n ↦ eval φ (ℳ n)`. -/
def hilbertFunction {A : Type u} {M : Type v}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    (φ : Module.EulerPoincareFunction A) (ℳ : ℤ → Submodule A M)
    [Decomposition ℳ] [LocallyFinite ℳ] : ℤ → ℤ :=
  fun n ↦ eval φ (ℳ n)

/-- The Hilbert function at degree `n` is the Euler-Poincaré value of the degree-`n` piece. -/
theorem hilbertFunction_apply {A : Type u} {M : Type v}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    (φ : Module.EulerPoincareFunction A) (ℳ : ℤ → Submodule A M)
    [Decomposition ℳ] [LocallyFinite ℳ] (n : ℤ) :
    hilbertFunction φ ℳ n = eval φ (ℳ n) := sorry

/-- A locally finite ℤ-graded module has a Hilbert polynomial when its Hilbert function
eventually agrees with a numerical polynomial. -/
def HasHilbertPolynomial {A : Type u} {M : Type v}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    (φ : Module.EulerPoincareFunction A) (ℳ : ℤ → Submodule A M)
    [Decomposition ℳ] [LocallyFinite ℳ] : Prop :=
  IsNumericalPolynomial (hilbertFunction φ ℳ)

end GradedModule
