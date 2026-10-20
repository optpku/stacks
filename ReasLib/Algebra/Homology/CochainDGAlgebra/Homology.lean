/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra

/-!
# Cycle Representatives in a Cochain Differential Graded Algebra

This leaf supplies a controlled representative for a homology class.  Its public API is the
projection formula, so constructions made from the representative can prove independence from
the projective choice.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A chosen cycle representing a cohomology class of a cochain differential graded algebra.
Downstream constructions should use `homologyπ_homologyCycle` (and the representative-independence
lemmas of the operation that consumes it) rather than inspect this quotient representative. -/
@[stacks 09S8 "chosen cycle representatives for cochain-DGA cohomology"]
noncomputable def homologyCycle (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (x : A.homology k) :
    A.cycles k :=
  (A.toCochainComplex.sc k).moduleCatCyclesIso.inv
    (Quotient.out ((A.toCochainComplex.sc k).moduleCatHomologyIso.hom x))

/-- The chosen cycle projects to the cohomology class that it represents. -/
@[simp, stacks 09S8 "cohomology class represented by the chosen cycle"]
theorem homologyπ_homologyCycle (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (x : A.homology k) :
    ModuleCat.Hom.hom (A.homologyπ k) (A.homologyCycle k x) = x := sorry

end CochainDGAlgebra
