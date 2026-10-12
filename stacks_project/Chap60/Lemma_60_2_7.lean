/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u

/- Lemma 60.2.7: flat quotient base change makes the canonical map from the
tensor product of a universal divided-power envelope to the new universal
envelope an isomorphism. -/
@[stacks 07HE] #check (DividedPowerEnvelope.baseChange :
  ∀ {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    {I J : Ideal B} (γ : DividedPowers I)
    (hIJ : Ideal.map (RingHom.id B) I ≤ J)
    (E : DividedPowerEnvelope I γ (RingHom.id B) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (RingHom.id B) hIJ E)
    {I' J' : Ideal B'} (γ' : DividedPowers I')
    (hγ : DividedPowers.IsDPMorphism γ γ' (algebraMap B B'))
    (hJ' : J' = Ideal.map (algebraMap B B') J + I')
    (hI' : Ideal.map (RingHom.id B') I' ≤ J')
    (E' : DividedPowerEnvelope I' γ' (RingHom.id B') J' hI')
    (hE' : DividedPowerEnvelope.IsUniversal γ' (RingHom.id B') hI' E')
    [Algebra B E.D] (hbase : algebraMap B E.D = E.toD)
    [Algebra B' E'.D] (hbase' : algebraMap B' E'.D = E'.toD)
    (hflat : RingHom.Flat (Ideal.quotientMap I' (algebraMap B B')
      (Ideal.map_le_iff_le_comap.mp hγ.ideal_comp))),
    Function.Bijective
      (DividedPowerEnvelope.baseChangeMap γ hIJ E hE γ' hγ hJ' hI' E' hbase hbase'))
