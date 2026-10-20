/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Tor.Vanishing
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Kunneth
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded

@[expose] public section

/-!
# The Künneth sequence over a Dedekind domain

@stack 0H80
-/

open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.Kunneth

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- Example 15.64.5 (1), tag `0H80`: over a Dedekind domain, `Tor_i(M, N)`
vanishes in every degree strictly above one. -/
@[stacks 0H80 "(1)"]
theorem torIsZeroAboveOne (M N : ModuleCat R) :
    ModuleCat.Tor.IsZeroAbove M N 1 := sorry

/-- Example 15.64.5 (2), tag `0H80`: a bounded Künneth spectral sequence
over a Dedekind domain degenerates at its second page. -/
@[stacks 0H80 "(2)"]
theorem degeneratesAtTwo
    (K L : DerivedCategory.Bounded (ModuleCat R))
    (E : CohomologicalSpectralSequence (ModuleCat R) 0)
    (hE : IsKunnethDerivedTensorSpectralSequence E K L) :
    (CohomologicalSpectralSequence.Page.One.ofZero E).degeneratesAt 2 := sorry

/-- Example 15.64.5 (3), tag `0H80`: the two surviving columns of the
Künneth spectral sequence form the canonical short exact sequence. -/
@[stacks 0H80 "(3)"]
theorem existsShortExactSequence
    (K L : DerivedCategory.Bounded (ModuleCat R)) (n : ℤ) :
    ∃ (ι : kunnethDerivedTensorPageTwo K L 0 n ⟶
          boundedDerivedTensorCohomology K L n)
      (π : boundedDerivedTensorCohomology K L n ⟶
          kunnethDerivedTensorPageTwo K L (-1) (n + 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end CategoryTheory.Kunneth
