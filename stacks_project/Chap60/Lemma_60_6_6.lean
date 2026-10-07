module

public import ReasLib.RingTheory.DividedPowers.Envelope.Differential
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 60.6.6: the composite base map is `E.base.toRingHom` by `E.base_toD`,
and bijectivity expresses the canonical differential-module identification. -/
@[stacks 07HW] #check (DividedPowerEnvelope.differentialComparison_bijective :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} (γ : DividedPowers I) (f : A →+* B)
    {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
    (E : DividedPowerEnvelope I γ f J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ f hIJ E),
    -- Local instance justification (noncanonical choice): use the explicit ring map `f` for the `A`-algebra structure on `B`.
    letI : Algebra A B := f.toAlgebra
    -- Local instance justification (noncanonical choice): use the explicit ring map `E.toD` for the `B`-algebra structure on `E.D`.
    letI : Algebra B E.D := E.toD.toAlgebra
    -- Local instance justification (noncanonical choice): use the explicit composite ring map `E.toD.comp f` for the `A`-algebra structure on `E.D`.
    letI : Algebra A E.D := (E.toD.comp f).toAlgebra
    -- Local instance justification (defeq pin): identify the composite scalar action through `B` with the pinned `A`-algebra structure on `E.D`.
    letI : IsScalarTower A B E.D := IsScalarTower.of_algebraMap_eq' rfl
    Function.Bijective (DividedPowerEnvelope.differentialComparison E))
