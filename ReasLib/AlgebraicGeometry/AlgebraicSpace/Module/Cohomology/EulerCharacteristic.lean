/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Field
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import Mathlib.Algebra.Homology.EulerCharacteristic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {k : Type u} [Field k]

/-- Each cohomology group of a coherent module on an algebraic space proper over a field is
finite dimensional over that field. -/
instance cohomologyFiniteDimensional (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [Proper (SchemeRealization.toBase X)] (F : Modules X) [IsCoherent F] (degree : ℕ) :
    FiniteDimensional k (cohomology F degree) := sorry

/-- The cohomology of a coherent module on a proper algebraic space vanishes in all
sufficiently large degrees. -/
theorem cohomology_eventually_subsingleton (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [Proper (SchemeRealization.toBase X)] (F : Modules X) [IsCoherent F] :
    ∃ bound : ℕ, ∀ degree : ℕ, bound ≤ degree → Subsingleton (cohomology F degree) := sorry

/-- The Euler characteristic of a coherent module on an algebraic space proper over a field
is the signed finite sum of its cohomology dimensions over that field. -/
def eulerCharacteristic (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [Proper (SchemeRealization.toBase X)] (F : Modules X) [IsCoherent F] : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ)
    (fun degree : ℕ => ModuleCat.of k (cohomology F degree))

/-- The Euler characteristic equals the alternating sum of the dimensions of small étale
cohomology over the base field. -/
theorem eulerCharacteristic_def (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [Proper (SchemeRealization.toBase X)] (F : Modules X) [IsCoherent F] :
    eulerCharacteristic X F =
      ∑ᶠ degree : ℕ,
        ((degree : ℤ).negOnePow : ℤ) * (Module.finrank k (cohomology F degree) : ℤ) := sorry

/-- A bound beyond which cohomology vanishes computes the Euler characteristic by the
alternating sum over the degrees strictly below that bound. -/
theorem eulerCharacteristic_eq_sum_range (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [Proper (SchemeRealization.toBase X)] (F : Modules X) [IsCoherent F] (bound : ℕ)
    (h_vanishing : ∀ degree : ℕ, bound ≤ degree → Subsingleton (cohomology F degree)) :
    eulerCharacteristic X F =
      ∑ degree ∈ Finset.range bound,
        ((degree : ℤ).negOnePow : ℤ) * (Module.finrank k (cohomology F degree) : ℤ) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
