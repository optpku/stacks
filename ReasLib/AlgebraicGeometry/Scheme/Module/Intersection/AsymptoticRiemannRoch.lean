/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Positivity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.RingTheory.Polynomial.Evaluation

/-!
# Asymptotic Riemann–Roch

This file records the eventual Hilbert polynomial of powers of an ample invertible module on a
proper scheme over a field, including its degree, leading coefficient, and positivity.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
variable (L : X.Modules) [Invertible L] [IsAmple L]
variable {d : ℕ}

/-- The dimensions of global sections of natural powers of an ample invertible module on a
proper scheme are eventually represented by a polynomial of the scheme's dimension, whose
leading coefficient is the whole-scheme intersection degree divided by the dimension factorial
and is positive. -/
theorem exists_asymptoticRiemannRochPolynomial
    (hXdim : topologicalKrullDim X = d) :
    ∃ P : Polynomial ℚ,
      P.EventuallyEqNat
          (fun n ↦ (Scheme.Hom.cohomologyFinrank f (L ^⊗ (n : ℤ)) 0 : ℚ)) ∧
        P.natDegree = d ∧
        P.leadingCoeff =
          Scheme.Modules.Intersection.wholeDegree k f L hXdim /
            (Nat.factorial d : ℚ) ∧
        0 < P.leadingCoeff := sorry

end AlgebraicGeometry.Scheme.Modules
