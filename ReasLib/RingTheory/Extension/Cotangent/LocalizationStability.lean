/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.PresentationStability

/-!
# Stable Cotangent Modules after Localization

@stack 00S6

This leaf records the stable conormal comparison between a finite presentation
and a finite presentation after localizing away from one element.  The
coordinate-free presentation stability is provided by
`Algebra.Generators.Cotangent.stableEquiv`.
-/

@[expose] public section

open Algebra

universe u v

namespace Algebra.Generators.Cotangent.Localization

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {g : S} {n m : ℕ}

/-- Lemma 10.134.16, tag `00S6`: localizing the conormal module of a finite presentation away
from `g` is stably equivalent to the conormal module of every finite presentation of
`Localization.Away g`. -/
@[stacks 00S6 "localized presentation cotangent stabilization"]
theorem stableEquivAway
    (P : Generators R S (Fin n)) (Q : Generators R (Localization.Away g) (Fin m)) :
    Nonempty
      ((LocalizedModule.Away g P.toExtension.Cotangent × (Fin m →₀ Localization.Away g)) ≃ₗ[
        Localization.Away g] (Q.toExtension.Cotangent × (Fin n →₀ Localization.Away g))) := sorry

end Algebra.Generators.Cotangent.Localization
