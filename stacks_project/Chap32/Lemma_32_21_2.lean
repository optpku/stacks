/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.Properties
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 32.21.2 (1): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is separated if and only if `g` is separated. -/
@[stacks 0BFN] #check
  (AlgebraicGeometry.puncturedLocalBaseChange.isSeparated_iff :
    ∀ (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
      (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
      (hUqc : QuasiCompact U.ι)
      (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
      (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
        ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
          Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
      (X : FinitePresentationIsoOverOpen U)
      (Y : FinitePresentationIsoOverOpen V)
      (e : (AlgebraicGeometry.puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y),
      IsSeparated X.obj.hom ↔ IsSeparated Y.obj.hom)

/- Lemma 32.21.2 (2): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is proper if and only if `g` is proper. -/
@[stacks 0BFN] #check
  (AlgebraicGeometry.puncturedLocalBaseChange.isProper_iff :
    ∀ (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
      (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
      (hUqc : QuasiCompact U.ι)
      (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
      (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
        ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
          Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
      (X : FinitePresentationIsoOverOpen U)
      (Y : FinitePresentationIsoOverOpen V)
      (e : (AlgebraicGeometry.puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y),
      IsProper X.obj.hom ↔ IsProper Y.obj.hom)

/- Lemma 32.21.2 (3): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is finite if and only if `g` is finite. -/
@[stacks 0BFN] #check
  (AlgebraicGeometry.puncturedLocalBaseChange.isFinite_iff :
    ∀ (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
      (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
      (hUqc : QuasiCompact U.ι)
      (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
      (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
        ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
          Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
      (X : FinitePresentationIsoOverOpen U)
      (Y : FinitePresentationIsoOverOpen V)
      (e : (AlgebraicGeometry.puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y),
      IsFinite X.obj.hom ↔ IsFinite Y.obj.hom)

/- Lemma 32.21.2 (4): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is étale if and only if `g` is étale. -/
@[stacks 0BFN] #check
  (AlgebraicGeometry.puncturedLocalBaseChange.etale_iff :
    ∀ (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
      (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
      (hUqc : QuasiCompact U.ι)
      (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
      (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
        ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
          Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
      (X : FinitePresentationIsoOverOpen U)
      (Y : FinitePresentationIsoOverOpen V)
      (e : (AlgebraicGeometry.puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y),
      Etale X.obj.hom ↔ Etale Y.obj.hom)

/- Lemma 32.21.2 (5): in the notation and assumptions of Lemma 32.21.1, if
`f : X ⟶ S` corresponds to `g : Y ⟶ Spec(𝒪_{S,s})` via the punctured-local equivalence, then
`f` is integral if and only if `g` is integral. -/
@[stacks 0BFN] #check
  (AlgebraicGeometry.puncturedLocalBaseChange.isIntegralHom_iff :
    ∀ (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
      (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
      (hUqc : QuasiCompact U.ι)
      (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
      (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
        ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
          Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ)
      (X : FinitePresentationIsoOverOpen U)
      (Y : FinitePresentationIsoOverOpen V)
      (e : (AlgebraicGeometry.puncturedLocalBaseChange S s hs U hU hUqc V hV).obj X ≅ Y),
      IsIntegralHom X.obj.hom ↔ IsIntegralHom Y.obj.hom)
