module
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.TotallySplit
import StacksCheckRecall

/-!
@stack 02JI
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain triage:
* primary domain: localization images on prime spectra and idempotent splittings of commutative
  rings;
* sampled owner declarations:
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `algebraMap_surjective_of_isClosed_range_comap`,
  `IsLocalization.away_of_isIdempotentElem`,
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
* best owner abstraction: the image of `Spec(S⁻¹R) → Spec(R)` as a clopen/basic-open subset,
  classified by an idempotent and then converted to a canonical product decomposition;
* layer: `source-facing`, since Lemma 10.33.2 adds the textbook closed-image-to-product statement
  rather than merely recalling one owner theorem.

Primitive-vs-derived split:
* primitive data: the submonoid `S`, the closedness of the image of `Spec(S⁻¹R) → Spec(R)`, and
  the auxiliary hypothesis that `Spec(R)` is Noetherian or `S` is finitely generated;
* derived API: the unique idempotent cutting out that image, the induced `Away e` comparison, and
  the product decomposition `R ≃ Localization S × R/(e)`.
-/

universe u

open PrimeSpectrum TopologicalSpace

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)

-- Local declaration justification (source-local notation): all three source-facing views use the
-- same localization image, and naming it keeps their hypotheses and conclusions readable.
local notation "imageSet" => Set.range (comap (algebraMap R (Localization S)))

/-- A closed localization image is clopen when the prime spectrum is Noetherian or the localizing
submonoid is finitely generated. -/
@[stacks 02JI "clopen localization image"]
theorem isClopen_range_comap_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    IsClopen imageSet := sorry

/-- An idempotent companion to Lemma 10.33.2: under the source hypotheses, the localization image
is the basic open `D(e)` of a unique idempotent `e`. -/
@[stacks 02JI "idempotent basic-open companion"]
theorem existsUnique_idempotent_basicOpen_eq_range_comap_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃! e : R, IsIdempotentElem e ∧ imageSet = basicOpen e := sorry

/-- A canonical quotient-factor companion to Lemma 10.33.2: under the source hypotheses, an
idempotent `e` gives an `R`-algebra decomposition `R ≃ S⁻¹R × R/(e)`. -/
@[stacks 02JI "canonical quotient-factor companion"]
theorem exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃ (e : R) (_ : IsIdempotentElem e)
      (φ : R ≃ₐ[R] (Localization S × (R ⧸ Ideal.span ({e} : Set R)))),
        (RingHom.fst (Localization S) (R ⧸ Ideal.span ({e} : Set R))).comp φ.toRingHom =
          algebraMap R (Localization S) := sorry

/-- Lemma 10.33.2: if the image of `Spec(S⁻¹R) → Spec(R)` is closed and either `Spec(R)` is a
Noetherian topological space or `S` is finitely generated, then `R` is isomorphic to a product
`S⁻¹R × R'` for some commutative ring `R'`. -/
@[stacks 02JI "complementary product factor"]
theorem exists_complementary_factor_ringEquiv_localization_prod_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃ (R' : Type u) (_ : CommRing R') (φ : R ≃+* (Localization S × R')),
      (RingHom.fst (Localization S) R').comp φ.toRingHom = algebraMap R (Localization S) := sorry

end
