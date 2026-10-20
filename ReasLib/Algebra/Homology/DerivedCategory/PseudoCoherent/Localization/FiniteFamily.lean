/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherence on finite principal-open covers

This leaf specializes the set-indexed principal-open localization criteria to a finite family of
ring elements whose span is the unit ideal.  The family presentation is useful at source-facing
and computational boundaries, while `of_localizationSpan` remains the canonical set-indexed core.

@stack 066D
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type u} [CommRing R]
variable {ι : Type w} [Finite ι]

/-- Lemma 15.65.14 (1) (066D): `m`-pseudo-coherence descends from a finite principal-open cover. -/
@[stacks 066D "(1) m-pseudo-coherence on a finite principal-open cover"]
theorem of_localizationAway_unitIdeal (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    {K : DerivedCategory (ModuleCat.{v, u} R)} {m : ℤ}
    (hloc : ∀ i,
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap R (Localization.Away (f i)))).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry
-- Proof strategy: apply `of_localizationSpan` to `Set.range f`; choose a preimage index for each
-- element of the range and discharge the localized hypothesis with `hloc`.

/-- `m`-pseudo-coherence is equivalent to `m`-pseudo-coherence on every member of a finite
principal-open cover. -/
@[stacks 066D "m-pseudo-coherence criterion on a finite principal-open cover"]
theorem iff_localizationAway_unitIdeal (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ∀ i,
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away (f i)))).obj K).IsMPseudoCoherent m := sorry
-- Proof strategy: combine `of_localizationAway_unitIdeal` with preservation of
-- `IsMPseudoCoherent` under derived extension of scalars.

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [CommRing R]
variable {ι : Type w} [Finite ι]

/-- Lemma 15.65.14 (2) (066D): pseudo-coherence descends from a finite principal-open cover. -/
@[stacks 066D "(2) pseudo-coherence on a finite principal-open cover"]
theorem of_localizationAway_unitIdeal (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    {K : DerivedCategory (ModuleCat.{v, u} R)}
    (hloc : ∀ i,
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap R (Localization.Away (f i)))).obj K).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry
-- Proof strategy: apply `of_localizationSpan` to `Set.range f`; choose a preimage index for each
-- element of the range and discharge the localized hypothesis with `hloc`.

/-- Pseudo-coherence is equivalent to pseudo-coherence on every member of a finite principal-open
cover. -/
@[stacks 066D "pseudo-coherence criterion on a finite principal-open cover"]
theorem iff_localizationAway_unitIdeal (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{v, u} R)) :
    K.IsPseudoCoherent ↔
      ∀ i,
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away (f i)))).obj K).IsPseudoCoherent := sorry
-- Proof strategy: combine `of_localizationAway_unitIdeal` with preservation of
-- `IsPseudoCoherent` under derived extension of scalars.

end CategoryTheory.DerivedCategory.IsPseudoCoherent
