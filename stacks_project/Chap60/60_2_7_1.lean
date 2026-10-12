/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Presentation.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v

/- 60.2.7.1: the base-changed universal divided-power envelope is the polynomial
algebra over the new base modulo the images of its original presentation relations. -/
@[stacks 07HF] #check (DividedPowerEnvelope.baseChangePresentation :
    ∀
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (RingHom.id B) hIJ E)
    {ι : Type v} (f : ι → B) (hf : ∀ i, f i ∈ J)
    (hgen : J = I + Ideal.span (Set.range f))
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : I' ≤ J')
    [Algebra B E.D]
    (hbase : algebraMap B E.D = E.toD)
    (hflat : RingHom.Flat
      (Ideal.quotientMap I' (algebraMap B B')
        (Ideal.map_le_iff_le_comap.mp hγ.ideal_comp))),
    let K : Ideal (DPPolynomial B ι) :=
      Ideal.span (DividedPowerEnvelope.presentationRelations γ f)
    let K' : Ideal (DPPolynomial B' ι) :=
      Ideal.map (DPPolynomial.map (DividedPowers.DPMorphism.mk' hγ)).toRingHom K
    TensorProduct B E.D B' ≃ₐ[B'] (DPPolynomial B' ι ⧸ K'))
