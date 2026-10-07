module

public import ReasLib.RingTheory.DividedPowers.Polynomial
public import ReasLib.RingTheory.DividedPowers.Envelope.Universal

@[expose] public section

open DividedPowers

universe u v

namespace DividedPowerEnvelope

/-- The variable and positive divided-power coefficient relations for the presentation of an
envelope. -/
def presentationRelations
    {B : Type u} [CommRing B] {I : Ideal B} (γ : DividedPowers I)
    {T : Type v} (f : T → B) : Set (DPPolynomial B T) :=
  Set.range (fun t : T ↦
    DPPolynomial.X B t - algebraMap B (DPPolynomial B T) (f t)) ∪
    {x | ∃ (n : ℕ) (r : T →₀ B) (r₀ : B),
      n ≠ 0 ∧ r₀ ∈ I ∧ r.sum (fun t a ↦ a * f t) = r₀ ∧
        x = dpow (DPPolynomial.dividedPowers γ) n
          (r.sum (fun t a ↦ algebraMap B (DPPolynomial B T) a * DPPolynomial.X B t) -
            algebraMap B (DPPolynomial B T) r₀)}

/-- Every variable relation belongs to `presentationRelations`. -/
theorem presentationRelations_variable_mem
    {B : Type u} [CommRing B] {I : Ideal B} (γ : DividedPowers I)
    {T : Type v} (f : T → B) (t : T) :
    DPPolynomial.X B t - algebraMap B (DPPolynomial B T) (f t) ∈
      presentationRelations γ f := sorry

/-- Every positive divided-power coefficient relation belongs to `presentationRelations`. -/
theorem presentationRelations_dpow_mem
    {B : Type u} [CommRing B] {I : Ideal B} (γ : DividedPowers I)
    {T : Type v} (f : T → B) (n : ℕ) (r : T →₀ B) (r₀ : B)
    (hn : n ≠ 0) (hr₀ : r₀ ∈ I) (hrel : r.sum (fun t a ↦ a * f t) = r₀) :
    dpow (DPPolynomial.dividedPowers γ) n
        (r.sum (fun t a ↦ algebraMap B (DPPolynomial B T) a * DPPolynomial.X B t) -
          algebraMap B (DPPolynomial B T) r₀) ∈ presentationRelations γ f := sorry

/-- The canonical divided-power morphism from the polynomial presentation to an envelope. -/
noncomputable def presentationMap
    {B : Type u} [CommRing B] {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    {T : Type v} (f : T → B) (hf : ∀ t, f t ∈ J) :
    DividedPowers.DPMorphism
      (DPPolynomial.dividedPowers γ : DividedPowers (DPPolynomial.ideal B T I))
      E.D.dividedPowers :=
  DPPolynomial.dpLift E.base
    (fun t ↦ ⟨E.toD (f t), E.ideal_map (Ideal.mem_map_of_mem E.toD (hf t))⟩)

/-- The presentation morphism sends each formal variable to the corresponding envelope element. -/
@[simp]
theorem presentationMap_apply_X
    {B : Type u} [CommRing B] {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    {T : Type v} (f : T → B) (hf : ∀ t, f t ∈ J) (t : T) :
    presentationMap γ hIJ E f hf (DPPolynomial.X B t) = E.toD (f t) := sorry

/-- The presentation morphism restricts to the envelope base map on coefficients. -/
theorem presentationMap_comp_algebraMap
    {B : Type u} [CommRing B] {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    {T : Type v} (f : T → B) (hf : ∀ t, f t ∈ J) :
    (presentationMap γ hIJ E f hf).toRingHom.comp
        (algebraMap B (DPPolynomial B T)) = E.base.toRingHom := sorry

/-- For generators of an ideal over the base divided-power ideal, the canonical polynomial
presentation map to a universal envelope is surjective and sends each variable to its generator. -/
theorem presentationMap_surjective
    {B : Type u} [CommRing B] {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (RingHom.id B) hIJ E)
    {T : Type v} (f : T → B) (hf : ∀ t, f t ∈ J)
    (hgen : J = I + Ideal.span (Set.range f)) :
    Function.Surjective (presentationMap γ hIJ E f hf).toRingHom ∧
      ∀ t : T, presentationMap γ hIJ E f hf (DPPolynomial.X B t) = E.toD (f t) := sorry

/-- For generators of an ideal over the base divided-power ideal, the kernel of the canonical
presentation map to a universal envelope is spanned by the variable and positive divided-power
coefficient relations. -/
theorem presentationMap_kernel
    {B : Type u} [CommRing B] {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (RingHom.id B) hIJ E)
    {T : Type v} (f : T → B) (hf : ∀ t, f t ∈ J)
    (hgen : J = I + Ideal.span (Set.range f)) :
    RingHom.ker (presentationMap γ hIJ E f hf).toRingHom =
      Ideal.span (presentationRelations γ f) := sorry

end DividedPowerEnvelope
