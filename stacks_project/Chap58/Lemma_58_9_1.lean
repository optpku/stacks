/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Henselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.9.1: base change to the closed fibre of a proper scheme over a
henselian local ring is an equivalence on finite étale schemes. -/
@[stacks 0A48] #check (AlgebraicGeometry.Scheme.Hom.finiteEtaleBaseChangeIsEquivalence :
    ∀ {A : Type u} [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f],
      Functor.IsEquivalence
        (Scheme.finiteEtaleBaseChange (f.fiberι (IsLocalRing.closedPoint A))))
