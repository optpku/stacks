/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.RingTheory.Coherent.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherent modules over coherent rings

@stack 0EWZ

This narrow leaf owns the degree-zero module bridge used in the proof of the coherent-ring
criteria.  It does not import the derived-category t-structure.
-/

open CategoryTheory

universe u v

namespace Module

variable {R : Type u} [Ring R] [Module.Coherent R R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a coherent ring, a module is pseudo-coherent exactly when it is coherent. -/
@[stacks 0EWZ "coherent module bridge for pseudo-coherence"]
theorem isPseudoCoherent_iff_coherent [Small.{v} R] :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Coherent R M := sorry
-- Proof strategy: evaluate pseudo-coherence at degree `-1`, use the finite-presentation
-- characterization there, and convert finite presentation to coherence; conversely build a
-- finite-free resolution recursively from coherence of kernels.

end Module
