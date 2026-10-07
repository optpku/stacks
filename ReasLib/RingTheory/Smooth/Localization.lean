module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localization of Smooth Ring Homomorphisms

@stack 00T3
@stack 00T7

These ring-hom theorems are the intrinsic localization API for smoothness.
The algebra-facing corollaries retain the common `algebraMap` spelling without
requiring consumers to reconstruct a ring-hom smoothness witness.
-/

universe u v w

namespace RingHom.Smooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.137.2 (1), tag `00T3`: localizing the target of a smooth ring
homomorphism away from any element preserves smoothness. -/
@[stacks 00T3 "smoothness under target localization"]
theorem localizationAway {f : R →+* S} (hf : f.Smooth) (g : S) :
    ((algebraMap S (Localization.Away g)).comp f).Smooth := sorry

/-- Lemma 10.137.2 (2), tag `00T3`: if `r` becomes a unit under a smooth ring
homomorphism, its induced map from the away-localization is smooth. -/
@[stacks 00T3 "smoothness under source localization"]
theorem awayLift {f : R →+* S} (hf : f.Smooth) (r : R) (hr : IsUnit (f r)) :
    (Localization.awayLift f r hr).Smooth := sorry

end RingHom.Smooth

namespace Algebra.Smooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A smooth `R`-algebra remains smooth after localizing its target away from
any element. -/
theorem localizationAway [Algebra.Smooth R S] (g : S) :
    Algebra.Smooth R (Localization.Away g) := sorry

/-- When an element of the base becomes a unit in a smooth `R`-algebra, the
induced map from the corresponding away-localization is smooth. -/
theorem awayLift [Algebra.Smooth R S] (r : R) (hr : IsUnit (algebraMap R S r)) :
    (Localization.awayLift (algebraMap R S) r hr).Smooth := sorry

end Algebra.Smooth

namespace Algebra.IsStandardSmooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.137.6 (2), tag `00T7`: standard smoothness is preserved by an
arbitrary target away-localization. -/
@[stacks 00T7 "standard smoothness under target localization"]
theorem localizationAway {Sg : Type w} [CommRing Sg] [Algebra R Sg] [Algebra S Sg]
    [IsScalarTower R S Sg] [hS : IsStandardSmooth R S] (g : S)
    [IsLocalization.Away g Sg] :
    IsStandardSmooth R Sg := sorry

variable {Rf : Type w} [CommRing Rf] [Algebra R Rf] [Algebra Rf S]
variable [IsScalarTower R Rf S]

/-- Lemma 10.137.6 (4), tag `00T7`: if an element of the base becomes a unit
in a standard smooth algebra, the induced algebra over its away-localization
is standard smooth. -/
@[stacks 00T7 "standard smoothness under source localization"]
theorem of_isUnit_base [hS : IsStandardSmooth R S] {f : R}
    [IsLocalization.Away f Rf] :
    IsStandardSmooth Rf S := sorry

end Algebra.IsStandardSmooth
