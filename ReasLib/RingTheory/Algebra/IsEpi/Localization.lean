/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.IsEpi

/-!
# Algebra epimorphisms and localization

Epimorphy of a commutative algebra is stable under base change and can be detected after
localizing the base at every maximal, hence every prime, ideal.  The localized target is modeled
canonically as the tensor-product base change.  The canonical principal-localization map is also
registered here as a reusable ring epimorphism.
@stack 091P
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Algebra.IsEpi

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- The forward implication of both local criteria is the general base-change API. -/

/-- An algebra is epic when its base change to every maximal localization of the base is epic. -/
@[stacks 04VS "maximal detection"]
theorem of_forall_atMaximal
    (h : ∀ m : MaximalSpectrum R,
      Algebra.IsEpi (Localization.AtPrime m.asIdeal)
        (Localization.AtPrime m.asIdeal ⊗[R] S)) :
    Algebra.IsEpi R S := sorry

/-- Epimorphy of an algebra is detected at the maximal localizations of the base. -/
@[stacks 04VS "maximal iff"]
theorem iff_forall_atMaximal :
    Algebra.IsEpi R S ↔
      ∀ m : MaximalSpectrum R,
        Algebra.IsEpi (Localization.AtPrime m.asIdeal)
          (Localization.AtPrime m.asIdeal ⊗[R] S) := sorry

/-- Lemma 10.107.5 (Stacks `04VS`): epimorphy of an algebra is detected at every prime
localization of the base. -/
@[stacks 04VS]
theorem iff_forall_atPrime :
    Algebra.IsEpi R S ↔
      ∀ p : PrimeSpectrum R,
        Algebra.IsEpi (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S) := sorry

end Algebra.IsEpi

namespace RingHom

variable {R : Type u} [CommRing R]

/- The principal localization is a particularly common epimorphic map.  Keeping this instance
in the shared ring-hom namespace lets module-category and derived-localization clients reuse it
without importing a chapter file. -/
/-- Stacks `091P`: the canonical map from `R` to `Localization.Away f` is an epimorphism. -/
@[stacks 091P "principal localization is a ring epimorphism"]
instance localizationAway_epi (f : R) :
    Epi (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := sorry

end RingHom
