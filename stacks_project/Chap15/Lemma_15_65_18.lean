/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Coherent
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Coherent.Module

import StacksCheckRecall

@[expose] public section

/-!
# Coherent-ring criteria for pseudo-coherence

@stack 0EWZ

Lemma 15.65.18 is recalled through the atomic coherent-tail, finite-presentation-tail, and
module-level owners in `PseudoCoherent.Coherent`; the textbook `TFAE` packaging is intentionally
not duplicated as a chapter-owned list.
-/

open CategoryTheory

universe u v

@[stacks 0EWZ "Lemma 15.65.18, (1) iff (2)"]
#check fun {R : Type u} [Ring R] [Module.Coherent R R]
    (K : DerivedCategory.Minus (ModuleCat.{v, u} R)) (m : ℤ) ↦
  (DerivedCategory.IsMPseudoCoherent.iff_finite_coherent_tail K m :
    K.obj.IsMPseudoCoherent m ↔
      Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) m).obj K.obj) ∧
        ∀ i : ℤ, m < i →
          Module.Coherent R
            ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K.obj))

@[stacks 0EWZ "Lemma 15.65.18, (1) iff (3)"]
#check fun {R : Type u} [Ring R] [Module.Coherent R R]
    (K : DerivedCategory.Minus (ModuleCat.{v, u} R)) (m : ℤ) ↦
  (DerivedCategory.IsMPseudoCoherent.iff_finitePresentation_tail K m :
    K.obj.IsMPseudoCoherent m ↔
      Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) m).obj K.obj) ∧
        ∀ i : ℤ, m < i →
          Module.FinitePresentation R
            ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K.obj))

@[stacks 0EWZ "Lemma 15.65.18, final assertion"]
#check fun {R : Type u} [Ring R] [Module.Coherent R R]
    (K : DerivedCategory.Minus (ModuleCat.{v, u} R)) ↦
  (DerivedCategory.IsPseudoCoherent.iff_homology_coherent K :
    K.obj.IsPseudoCoherent ↔
      ∀ i : ℤ,
        Module.Coherent R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K.obj))

/- The module bridge is proof infrastructure for the source equivalences, not a numbered source
clause. -/
#check fun {R : Type u} [Ring R] [Module.Coherent R R]
    {M : Type v} [AddCommGroup M] [Module R M] ↦
  (Module.isPseudoCoherent_iff_coherent (R := R) (M := M) :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Coherent R M)
