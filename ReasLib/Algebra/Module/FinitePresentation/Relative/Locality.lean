/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locality of relative finite presentation

Relative finite presentation may be checked on a finite principal-open cover. The reverse
implication also recovers finite type of the ambient algebra from the localized hypotheses.

@stack 065D
-/

@[expose] public section

universe u v w

namespace Module.FinitePresentationRelativeTo

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

/-- Stacks 065D: relative finite presentation is local on a finite family of principal opens
whose defining elements generate the unit ideal. -/
@[stacks 065D "principal-open locality of relative finite presentation"]
theorem iff_localizationAway_unitIdeal
    (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤) :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ f : s, Module.FinitePresentationRelativeTo R (Localization.Away f.1)
        (LocalizedModule.Away f.1 M) := sorry
/- Proof strategy: the forward implication applies
`finitePresentationRelativeTo_localizationAway_from_localizedBase` with the trivial source
localization.  Conversely, recover finite type of `A/R` from the finite principal cover and use
`iff_overEveryPolynomialPresentation`; Mathlib's finite-presentation locality theorem glues the
restricted module presentations because `hs` says the opens cover `Spec A`. -/

end Module.FinitePresentationRelativeTo
