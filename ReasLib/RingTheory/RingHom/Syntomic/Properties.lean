module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Syntomic.AtPrime
public import ReasLib.RingTheory.RingHom.Syntomic.BaseChange
public import ReasLib.RingTheory.RingHom.Syntomic.Composition

@[expose] public section

/-!
# Principal-Open Stability of Syntomic Ring Homomorphisms

This leaf exposes the forward target-localization interface that complements
the descent witnesses in `Syntomic.Localization`.  It is kept separate from
the individual stability leaves so that generic local-property consumers can
import these bridges without creating an import cycle.

@stack 00SO
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace HasLocalCompleteIntersectionFibers

/-- Lemma 10.136.4, tag `00SO`: localizing the target of a ring homomorphism
with local complete-intersection fibers preserves that fiber condition. -/
@[stacks 00SO "local complete-intersection fibers under target localization"]
theorem localizationAway {f : R →+* S} (hf : f.HasLocalCompleteIntersectionFibers) (g : S) :
    ((algebraMap S (Localization.Away g)).comp f).HasLocalCompleteIntersectionFibers := sorry

end HasLocalCompleteIntersectionFibers

namespace Syntomic

/-- Every principal localization map is syntomic. -/
theorem holdsForLocalizationAway : HoldsForLocalizationAway Syntomic := sorry

/-- Syntomicity is stable under composing on the target with an arbitrary
principal localization map. -/
theorem stableUnderCompositionWithLocalizationAwayTarget :
    StableUnderCompositionWithLocalizationAwayTarget Syntomic := sorry

/-- Syntomicity is a local property of commutative ring homomorphisms. -/
@[stacks 00SO "syntomicity is a local ring-homomorphism property"]
theorem propertyIsLocal : PropertyIsLocal Syntomic := sorry

/-- A ring homomorphism is syntomic exactly when it is syntomic on a
principal-open neighborhood of every target prime. -/
@[stacks 00SO "syntomicity from pointwise principal-open neighborhoods"]
theorem iff_forall_atPrime (f : R →+* S) :
    f.Syntomic ↔ ∀ q : PrimeSpectrum S, f.SyntomicAtPrime q := sorry

/-- Lemma 10.136.4, tag `00SO`: localizing the target of a syntomic ring
homomorphism away from any element preserves syntomicity. -/
@[stacks 00SO "syntomicity under target localization"]
theorem localizationAway {f : R →+* S} (hf : f.Syntomic) (g : S) :
    ((algebraMap S (Localization.Away g)).comp f).Syntomic := sorry

end Syntomic

end RingHom
