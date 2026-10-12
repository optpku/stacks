/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.DividedPowers.Envelope.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

/- Lemma 60.2.6. -/
@[stacks 07HD] #check (DividedPowerEnvelope.baseChange_of_quotient_flat_of_isZero_tor_one :
  ∀ {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    {I : Ideal A} (γ : DividedPowers I) {J : Ideal B}
    (hIJ : Ideal.map (algebraMap A B) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A B) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A B) hIJ E)
    (hIcomp : Ideal.map (algebraMap A B) I ≤
      (Ideal.map (algebraMap A B') I).comap (algebraMap B B'))
    (hflat : RingHom.Flat
      (Ideal.quotientMap (Ideal.map (algebraMap A B') I)
        (algebraMap B B') hIcomp))
    (htor : IsZero (Tor₁[B](B', B ⧸ Ideal.map (algebraMap A B) I)))
    (hIJ' : Ideal.map (algebraMap A B') I ≤ Ideal.map (algebraMap B B') J)
    (E' : DividedPowerEnvelope I γ (algebraMap A B')
      (Ideal.map (algebraMap B B') J) hIJ')
    (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A B') hIJ' E')
    [Algebra B E.D] (hbase : algebraMap B E.D = E.toD)
    [Algebra B' E'.D] (hbase' : algebraMap B' E'.D = E'.toD),
    Nonempty (TensorProduct B E.D B' ≃ₐ[B'] E'.D))
