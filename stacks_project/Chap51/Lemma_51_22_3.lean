/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CartierTwist
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

universe u

/- Lemma 51.22.3: for a coherent module on a blowup, annihilation by the
exceptional ideal power is equivalent to vanishing of the canonical negative twist map. -/
@[stacks 0GA9] #check (AlgebraicGeometry.IsBlowup.isAnnihilated_exceptionalDivisorPow_iff_canonicalTwistMap_eq_zero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    (c : ℕ) (F : X.Modules) [F.IsCoherent],
    IsAnnihilated
        (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject F ↔
      AlgebraicGeometry.IsBlowup.canonicalTwistMap I p F c = 0)
