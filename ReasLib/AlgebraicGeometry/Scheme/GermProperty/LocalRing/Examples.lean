module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing
public import ReasLib.RingTheory.Etale.LocalProperty.Examples

/-!
# Étale-local stalk properties

Noetherianity, dimension, regularity, discrete valuation, reducedness, normality,
Noetherian depth, Noetherian Cohen–Macaulayness, and Gorensteinness give étale-local
properties of scheme germs.
-/

@[expose] public section

universe u

open scoped ENat

namespace AlgebraicGeometry

/-- The germ property of having a Noetherian stalk is étale-local. -/
theorem ofLocalRing_isNoetherianRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsNoetherianRing R).IsEtaleLocal :=
  sorry

/-- The germ property of having stalk of Krull dimension `d` is étale-local. -/
theorem ofLocalRing_ringKrullDim_isEtaleLocal (d : WithBot ℕ∞) :
    (GermProperty.ofLocalRing fun R ↦ ringKrullDim R = d).IsEtaleLocal :=
  sorry

/-- The germ property of having a regular local stalk is étale-local. -/
theorem ofLocalRing_isRegularLocalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsRegularLocalRing R).IsEtaleLocal :=
  sorry

/-- The germ property of having a discrete valuation stalk is étale-local. -/
theorem ofLocalRing_isDiscreteValuationRing_isEtaleLocal :
    (GermProperty.ofLocalRing LocalRingProperty.isDiscreteValuationLocalRing).IsEtaleLocal :=
  sorry

/-- The germ property of having a reduced stalk is étale-local. -/
theorem ofLocalRing_isReduced_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ _root_.IsReduced R).IsEtaleLocal :=
  sorry

/-- The germ property of having a normal stalk is étale-local. -/
theorem ofLocalRing_isNormalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsNormalRing R).IsEtaleLocal :=
  sorry

/-- The germ property of having a Noetherian stalk of depth `k` is étale-local. -/
theorem ofLocalRing_isNoetherianOfDepth_isEtaleLocal (k : ℕ) :
    (GermProperty.ofLocalRing (LocalRingProperty.isNoetherianOfDepth k)).IsEtaleLocal :=
  sorry

/-- The germ property of having a Noetherian Cohen–Macaulay stalk is étale-local. -/
theorem ofLocalRing_isNoetherianCohenMacaulay_isEtaleLocal :
    (GermProperty.ofLocalRing LocalRingProperty.isNoetherianCohenMacaulay).IsEtaleLocal :=
  sorry

/-- The germ property of having a Gorenstein local stalk is étale-local. -/
theorem ofLocalRing_isGorensteinLocalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsGorensteinLocalRing R).IsEtaleLocal :=
  sorry

end AlgebraicGeometry
