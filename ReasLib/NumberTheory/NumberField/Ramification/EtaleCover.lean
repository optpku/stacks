/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
public import ReasLib.NumberTheory.NumberField.Ramification.Loci

/-!
# Étale covers from extensions of number fields

This file defines the morphism on spectra of rings of integers and its restriction over the
relative discriminant complement, together with the corresponding ramification properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped NumberField

noncomputable section

universe u

namespace NumberField.Ramification

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The morphism on spectra induced by the inclusion of rings of integers. -/
def specMap : Spec (.of (𝓞 L)) ⟶ Spec (.of (𝓞 K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) (𝓞 L)))

/-- On points, the spectrum morphism is contraction of prime ideals. -/
theorem specMap_apply (p : PrimeSpectrum (𝓞 L)) :
    specMap K L p = PrimeSpectrum.comap (algebraMap (𝓞 K) (𝓞 L)) p := sorry

/-- The restriction of the spectrum morphism over the relative discriminant complement. -/
def cover : (specMap K L ⁻¹ᵁ discriminantOpen K L).toScheme ⟶ discriminantOpen K L :=
  specMap K L ∣_ discriminantOpen K L

/-- Composing the restricted cover with its target open immersion recovers the spectrum
morphism on the inverse-image open. -/
theorem cover_comp_ι :
    cover K L ≫ (discriminantOpen K L).ι =
      (specMap K L ⁻¹ᵁ discriminantOpen K L).ι ≫ specMap K L := sorry

/-- Scheme-theoretic unramifiedness of the spectrum morphism at a prime is equivalent to
conventional unramifiedness of the corresponding extension of local rings. -/
theorem specMap_unramifiedAt_iff (p : PrimeSpectrum (𝓞 L)) :
    (specMap K L).UnramifiedAt p ↔ Algebra.IsUnramifiedAt (𝓞 K) p.asIdeal := sorry

/-- The morphism from the complement of the different to the base spectrum is unramified. -/
@[instance]
theorem differentCoverUnramified :
    Unramified ((differentOpen K L).ι ≫ specMap K L) := sorry

/-- The morphism from the complement of the different to the base spectrum is flat. -/
@[instance]
theorem differentCoverFlat : Flat ((differentOpen K L).ι ≫ specMap K L) := sorry

/-- The morphism from the complement of the different to the base spectrum is étale. -/
@[instance]
theorem differentCoverEtale : Etale ((differentOpen K L).ι ≫ specMap K L) := sorry

/-- For a Galois extension, the inverse image of the discriminant complement is the complement
of the different. -/
theorem preimageDiscriminantOpen_eq_differentOpen [IsGalois K L] :
    specMap K L ⁻¹ᵁ discriminantOpen K L = differentOpen K L := sorry

/-- The cover over the discriminant complement of a Galois extension is finite. -/
@[instance]
theorem galoisCoverFinite [IsGalois K L] : IsFinite (cover K L) := sorry

/-- The cover over the discriminant complement of a Galois extension is étale. -/
@[instance]
theorem galoisCoverEtale [IsGalois K L] : Etale (cover K L) := sorry

/-- The cover over the discriminant complement of a Galois extension is surjective. -/
@[instance]
theorem galoisCoverSurjective [IsGalois K L] : Surjective (cover K L) := sorry

end NumberField.Ramification
