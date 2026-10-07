module

public import ReasLib.RingTheory.DividedPowers.Envelope

@[expose] public section

universe u

/-- A divided-power envelope is universal when every compatible map from the presentation
factors uniquely through its envelope carrier. -/
def DividedPowerEnvelope.IsUniversal
    {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} (γ : DividedPowers I) (f : A →+* B)
    {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
    (E : DividedPowerEnvelope I γ f J hIJ) : Prop :=
  ∀ {T : DividedPowerRing.{u}} (φ : B →+* T),
    DividedPowers.IsDPMorphism γ T.dividedPowers (φ.comp f) →
    Ideal.map φ J ≤ T.ideal →
    ∃! ψ : E.D ⟶ T, ψ.toRingHom.comp E.toD = φ

/-- The universal mapping-property specification unfolds to the existence and uniqueness of
divided-power lifts through the envelope. -/
theorem DividedPowerEnvelope.IsUniversal_def
    {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} (γ : DividedPowers I) (f : A →+* B)
    {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
    (E : DividedPowerEnvelope I γ f J hIJ) :
    DividedPowerEnvelope.IsUniversal γ f hIJ E ↔
      ∀ {T : DividedPowerRing.{u}} (φ : B →+* T),
        DividedPowers.IsDPMorphism γ T.dividedPowers (φ.comp f) →
        Ideal.map φ J ≤ T.ideal →
        ∃! ψ : E.D ⟶ T, ψ.toRingHom.comp E.toD = φ := sorry

/-- For a divided-power ring `(A, I, γ)`, a ring map `f : A →+* B`, and an ideal `J`
containing `Ideal.map f I`, there exists a divided-power envelope with the universal
unique-lifting property for maps of ring-ideal pairs. -/
theorem DividedPowerEnvelope.existsUniversal
    {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} (γ : DividedPowers I) (f : A →+* B) (J : Ideal B)
    (hIJ : Ideal.map f I ≤ J) :
    ∃ E : DividedPowerEnvelope I γ f J hIJ,
      DividedPowerEnvelope.IsUniversal γ f hIJ E := sorry
