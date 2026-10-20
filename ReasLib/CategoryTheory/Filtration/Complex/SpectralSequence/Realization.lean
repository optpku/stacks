/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Realization of a Graded Family by a Filtered-Complex Spectral Sequence

This file records the common, representation-independent part of a spectral-sequence model:
association to a filtered complex and identification of the underlying cohomology with a
prescribed graded family. Page formulas and convergence hypotheses belong in specialized
extensions of this predicate.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A spectral sequence realizes the graded family `H` through the filtered complex `F` when it
is associated to `F` and the cohomology of the underlying complex is degreewise isomorphic to
`H`. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
structure Realizes (F : FilteredComplex C)
    (E : CohomologicalSpectralSequence C 0) (H : ℤ → C) : Prop where
  /-- The spectral sequence is associated to the filtered complex. -/
  associated : FilteredComplex.IsAssociated F E
  /-- The cohomology of the underlying complex realizes the prescribed graded family. -/
  abutment : ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ H n)

end CategoryTheory.FilteredComplex.SpectralSequence
