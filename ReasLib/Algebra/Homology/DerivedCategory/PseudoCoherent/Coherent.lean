/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.RingTheory.Coherent.FinitePresentation
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Coherent.Module
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Coherent-ring criteria for pseudo-coherence

@stack 0EWZ

For a coherent ring, bounded-above pseudo-coherence is measured by finite homology at the cutoff
and coherent (equivalently finitely presented) homology above it.  The API is split into atomic
criteria rather than exposing the source `List.TFAE` packaging.  The degree-zero module bridge is
kept in the narrower `PseudoCoherent.Coherent.Module` leaf.
-/

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type u} [Ring R] [Module.Coherent R R]

/-- Lemma 15.65.18, `(1) ↔ (2)`: finite cutoff homology and a coherent tail characterize
`m`-pseudo-coherence. -/
@[stacks 0EWZ "coherent-tail criterion for m-pseudo-coherence"]
theorem iff_finite_coherent_tail [Small.{v} R]
    (K : DerivedCategory.Minus (ModuleCat.{v, u} R)) (m : ℤ) :
    K.obj.IsMPseudoCoherent m ↔
      Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) m).obj K.obj) ∧
        ∀ i : ℤ, m < i →
          Module.Coherent R
            ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K.obj) := sorry
-- Proof strategy: extract the cutoff and higher homology conditions from a bounded finite-free
-- approximation; conversely apply the bounded-above homology criterion after resolving coherent
-- modules by finite free modules over the coherent ring.

/-- Lemma 15.65.18, `(1) ↔ (3)`: finite presentation can replace coherence in the homology
tail. -/
@[stacks 0EWZ "finite-presentation tail criterion for m-pseudo-coherence"]
theorem iff_finitePresentation_tail [Small.{v} R]
    (K : DerivedCategory.Minus (ModuleCat.{v, u} R)) (m : ℤ) :
    K.obj.IsMPseudoCoherent m ↔
      Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) m).obj K.obj) ∧
        ∀ i : ℤ, m < i →
          Module.FinitePresentation R
            ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K.obj) := sorry
-- Proof strategy: combine `iff_finite_coherent_tail` with
-- `module_coherent_iff_finitePresentation` for every homology module above the cutoff.

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [Ring R] [Module.Coherent R R]

/-- Lemma 15.65.18, final assertion: a bounded-above derived object is pseudo-coherent exactly
when all homology modules are coherent. -/
@[stacks 0EWZ "coherent homology criterion for pseudo-coherence"]
theorem iff_homology_coherent [Small.{v} R]
    (K : DerivedCategory.Minus (ModuleCat.{v, u} R)) :
    K.obj.IsPseudoCoherent ↔
      ∀ i : ℤ,
        Module.Coherent R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K.obj) := sorry
-- Proof strategy: use the all-degree characterization of pseudo-coherence and apply the coherent
-- tail criterion at a cutoff immediately below each requested homology degree.

end CategoryTheory.DerivedCategory.IsPseudoCoherent
