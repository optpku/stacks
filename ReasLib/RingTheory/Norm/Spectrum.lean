/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Norm.Projective
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Vanishing loci of algebra norms
-/

@[expose] public section

noncomputable section

universe u v

open PrimeSpectrum

namespace Algebra

/-- For a finite locally free algebra, the image of the vanishing locus of an element
is the vanishing locus of its norm. -/
theorem comap_zeroLocus_eq_zeroLocus_finiteProjectiveNorm
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (b : B) :
    comap (algebraMap A B) '' zeroLocus {b} =
      zeroLocus {finiteProjectiveNorm A b} := sorry

/-- A prime belongs to the image of an element's vanishing locus exactly when it contains
the finite-projective norm of that element. -/
theorem mem_comap_zeroLocus_finiteProjectiveNorm_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (b : B) (p : PrimeSpectrum A) :
    p ∈ comap (algebraMap A B) '' zeroLocus {b} ↔
      finiteProjectiveNorm A b ∈ p.asIdeal := sorry

end Algebra
