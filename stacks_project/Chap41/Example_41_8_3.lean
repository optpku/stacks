module

public import ReasLib.NumberTheory.NumberField.Ramification.EtaleCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped NumberField

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- Example 41.8.3 (1): the inclusion of rings of integers induces a morphism on spectra. -/
@[stacks 024Z] #check
  (NumberField.Ramification.specMap K L : Spec (.of (𝓞 L)) ⟶ Spec (.of (𝓞 K)))

/- Example 41.8.3 (2): scheme-theoretic and conventional pointwise unramifiedness agree. -/
@[stacks 024Z] #check
  (NumberField.Ramification.specMap_unramifiedAt_iff K L :
    ∀ p : PrimeSpectrum (𝓞 L),
      (NumberField.Ramification.specMap K L).UnramifiedAt p ↔
        Algebra.IsUnramifiedAt (𝓞 K) p.asIdeal)

/- Example 41.8.3 (3): the different is the annihilator of the module of Kähler differentials. -/
@[stacks 024Z] #check
  (NumberField.Ramification.differentIdeal_eq_annihilator K L :
    differentIdeal (𝓞 K) (𝓞 L) = Module.annihilator (𝓞 L) Ω[𝓞 L⁄𝓞 K])

/- Example 41.8.3 (4): the relative discriminant is an ideal in the base ring of integers. -/
@[stacks 024Z] #check
  (NumberField.Ramification.discriminantIdeal K L : Ideal (𝓞 K))

/- Example 41.8.3 (5): the relative discriminant is the relative norm of the different. -/
@[stacks 024Z] #check
  (NumberField.Ramification.discriminantIdeal_eq_relNorm K L :
    NumberField.Ramification.discriminantIdeal K L =
      Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L)))

/- Example 41.8.3 (6): the discriminant zero locus is the locus of ramified base primes. -/
@[stacks 024Z] #check
  (NumberField.Ramification.ramificationLocus_eq_zeroLocus K L :
    PrimeSpectrum.zeroLocus (NumberField.Ramification.discriminantIdeal K L).carrier =
      {p : PrimeSpectrum (𝓞 K) | ¬ Algebra.IsUnramifiedIn (𝓞 L) p.asIdeal})

/- Example 41.8.3 (7): the complement of the different defines an open subscheme. -/
@[stacks 024Z] #check
  (NumberField.Ramification.differentOpen K L : (Spec (.of (𝓞 L))).Opens)

/- Example 41.8.3 (8): the conventional unramified locus is the different complement. -/
@[stacks 024Z] #check
  (NumberField.Ramification.unramifiedLocus_eq_differentOpen K L :
    Algebra.unramifiedLocus (𝓞 K) (𝓞 L) =
      (NumberField.Ramification.differentOpen K L).carrier)

/- Example 41.8.3 (9): the morphism from the different complement is unramified. -/
@[stacks 024Z] #check
  (NumberField.Ramification.differentCoverUnramified K L :
    Unramified
      ((NumberField.Ramification.differentOpen K L).ι ≫
        NumberField.Ramification.specMap K L))

/- Example 41.8.3 (10): the morphism from the different complement is flat. -/
@[stacks 024Z] #check
  (NumberField.Ramification.differentCoverFlat K L :
    Flat
      ((NumberField.Ramification.differentOpen K L).ι ≫
        NumberField.Ramification.specMap K L))

/- Example 41.8.3 (11): the morphism from the different complement is étale. -/
@[stacks 024Z] #check
  (NumberField.Ramification.differentCoverEtale K L :
    Etale
      ((NumberField.Ramification.differentOpen K L).ι ≫
        NumberField.Ramification.specMap K L))

/- Example 41.8.3 (12): the complement of the discriminant defines an open subscheme. -/
@[stacks 024Z] #check
  (NumberField.Ramification.discriminantOpen K L : (Spec (.of (𝓞 K))).Opens)

section

variable [IsGalois K L]

/- Example 41.8.3 (13): for a Galois extension, the discriminant complement pulls back to the
different complement. -/
@[stacks 024Z] #check
  (NumberField.Ramification.preimageDiscriminantOpen_eq_differentOpen K L :
    NumberField.Ramification.specMap K L ⁻¹ᵁ
        NumberField.Ramification.discriminantOpen K L =
      NumberField.Ramification.differentOpen K L)

/- Example 41.8.3 (14): restricting over the discriminant complement gives the Galois cover. -/
@[stacks 024Z] #check
  (NumberField.Ramification.cover K L :
    (NumberField.Ramification.specMap K L ⁻¹ᵁ
          NumberField.Ramification.discriminantOpen K L).toScheme ⟶
      NumberField.Ramification.discriminantOpen K L)

/- Example 41.8.3 (15): the Galois cover over the discriminant complement is finite. -/
@[stacks 024Z] #check
  (NumberField.Ramification.galoisCoverFinite K L :
    IsFinite (NumberField.Ramification.cover K L))

/- Example 41.8.3 (16): the Galois cover over the discriminant complement is étale. -/
@[stacks 024Z] #check
  (NumberField.Ramification.galoisCoverEtale K L :
    Etale (NumberField.Ramification.cover K L))

/- Example 41.8.3 (17): the Galois cover over the discriminant complement is surjective. -/
@[stacks 024Z] #check
  (NumberField.Ramification.galoisCoverSurjective K L :
    Surjective (NumberField.Ramification.cover K L))

end
