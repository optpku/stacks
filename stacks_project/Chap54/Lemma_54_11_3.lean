/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

/- Lemma 54.11.3: an admissible blowup over the punctured spectrum of the
maximal-ideal completion of a Noetherian local ring descends to an admissible
blowup whose completion base-change square is cartesian. -/
@[stacks 0AFK] #check (AlgebraicGeometry.IsAdmissibleBlowup.exists_isPullback_of_completion :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ {Y : Scheme.{u}} (bHat : Y ⟶ Spec (.of Ahat)),
      IsAdmissibleBlowup (PuncturedSpectrum.puncturedOpen Ahat) bHat →
        ∃ (X : Scheme.{u}) (b : X ⟶ Spec (.of A)) (f : Y ⟶ X),
          IsAdmissibleBlowup (PuncturedSpectrum.puncturedOpen A) b ∧
            IsPullback f bHat b g)
