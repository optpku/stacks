/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Hilbert

/-!
# Hilbert functions of locally finite graded modules

The Hilbert function of a locally finite ℤ-graded `A`-module with respect to an Euler-Poincaré
function `φ` is the integer sequence of values of `φ` on the degree pieces. Having a Hilbert
polynomial means that this sequence is a numerical polynomial in the sense of
`IsNumericalPolynomial`.
-/

@[expose] public section

universe u v

variable {A : Type u} {M : Type v}
  [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]

#check (GradedModule.hilbertFunction :
  (φ : Module.EulerPoincareFunction.{u, v} A) → (ℳ : ℤ → Submodule A M) →
    [GradedModule.Decomposition ℳ] → [GradedModule.LocallyFinite ℳ] → ℤ → ℤ)

#check (GradedModule.HasHilbertPolynomial :
  (φ : Module.EulerPoincareFunction.{u, v} A) → (ℳ : ℤ → Submodule A M) →
    [GradedModule.Decomposition ℳ] → [GradedModule.LocallyFinite ℳ] → Prop)
