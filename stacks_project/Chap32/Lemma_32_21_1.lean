/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 32.21.1: let `S` be a scheme and let `s ∈ S` be a closed point. Let `U` satisfy
`(U : Set S) = ({s} : Set S)ᶜ`, with `U.ι` quasi-compact, and let `V` be the complement of the
closed point in `Spec(𝒪_{S,s})`. Base change along `S.fromSpecStalk s` is an equivalence between
finite-presentation morphisms that are isomorphisms over `U` and those that are isomorphisms over
`V`. -/
@[stacks 0B3X] #check
  (AlgebraicGeometry.puncturedLocalBaseChange_isEquivalence :
    ∀ (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
      (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
      (hUqc : QuasiCompact U.ι)
      (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
      (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
        ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
          Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ),
      Functor.IsEquivalence
        (AlgebraicGeometry.puncturedLocalBaseChange S s hs U hU hUqc V hV))
