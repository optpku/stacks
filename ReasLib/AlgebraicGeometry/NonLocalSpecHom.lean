module

public import ReasLib.AlgebraicGeometry.StalkToField
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# A non-local ringed-space morphism from `Spec ℚ` to `Spec ℤ`

The constant map to the closed point `(2)` is induced by the localization map
`ℤ_(2) → ℚ`. It is a morphism of ringed spaces but not a morphism of schemes.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.NonLocalSpecHom

/-- The spectrum of the ring of integers. -/
def intScheme : Scheme :=
  Spec (CommRingCat.of ℤ)

/-- The spectrum of the field of rational numbers. -/
def ratSpec : Scheme :=
  Spec (CommRingCat.of ℚ)

/-- The principal ideal `(2)` in the ring of integers. -/
def twoIdeal : Ideal ℤ :=
  Ideal.span {(2 : ℤ)}

/-- The closed point of `Spec ℤ` corresponding to the prime ideal `(2)`. -/
def twoPoint : PrimeSpectrum ℤ :=
  ⟨twoIdeal, (Ideal.span_singleton_prime (two_ne_zero : (2 : ℤ) ≠ 0)).mpr Int.prime_two⟩

/-- The stalk homomorphism at `(2)` induced by the inclusion of integers into
the rational numbers through localization. -/
def stalkHom : intScheme.presheaf.stalk twoPoint ⟶ CommRingCat.of ℚ :=
  CommRingCat.ofHom
    ((IsLocalization.lift (g := algebraMap ℤ ℚ)
        (fun y : twoPoint.asIdeal.primeCompl =>
          isUnit_iff_ne_zero.mpr
            (Int.cast_ne_zero.mpr
              (ne_of_mem_of_not_mem twoPoint.asIdeal.zero_mem y.2).symm))).comp
      (StructureSheaf.stalkIso ℤ twoPoint).symm.toRingHom)

/-- The morphism of ringed spaces from `Spec ℚ` to `Spec ℤ` induced by the
localization inclusion at `(2)`. -/
def hom : ratSpec.toSheafedSpace ⟶ intScheme.toSheafedSpace :=
  Scheme.ringedSpaceHomOfStalkHom twoPoint stalkHom

/-- The unique point of `Spec ℚ` is sent to `(2)` by the induced morphism. -/
theorem hom_apply (p : ratSpec) : hom.hom p = twoPoint :=
  sorry

/-- The homomorphism from the stalk of `Spec ℤ` at `(2)` to `ℚ` is not local. -/
theorem not_isLocalHom_stalkHom : ¬ IsLocalHom stalkHom.hom :=
  sorry

/-- The stalk map of the induced ringed-space morphism at the unique point of
`Spec ℚ` is not a local ring homomorphism. -/
theorem not_isLocalHom_stalkMap :
    ¬ IsLocalHom (hom.hom.stalkMap (closedPoint ℚ)).hom :=
  sorry

/-- The ringed-space morphism from `Spec ℚ` to `Spec ℤ` induced by the
localization inclusion at `(2)` does not underlie a morphism of schemes. -/
theorem not_isSchemeHom :
    ¬ ∃ f : ratSpec ⟶ intScheme,
      LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom = hom :=
  sorry

end AlgebraicGeometry.NonLocalSpecHom
