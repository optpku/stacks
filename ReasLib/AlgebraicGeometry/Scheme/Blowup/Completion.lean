/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.BaseChange

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.IsAdmissibleBlowup

/-- An admissible blowup over the punctured spectrum of the maximal-ideal completion of a
Noetherian local ring descends to an admissible blowup over the original punctured spectrum,
with a cartesian completion base-change square. -/
theorem exists_isPullback_of_completion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ {Y : Scheme.{u}} (bHat : Y ⟶ Spec (.of Ahat)),
      IsAdmissibleBlowup (PuncturedSpectrum.puncturedOpen Ahat) bHat →
        ∃ (X : Scheme.{u}) (b : X ⟶ Spec (.of A)) (f : Y ⟶ X),
          IsAdmissibleBlowup (PuncturedSpectrum.puncturedOpen A) b ∧
            IsPullback f bHat b g := sorry

end AlgebraicGeometry.IsAdmissibleBlowup
