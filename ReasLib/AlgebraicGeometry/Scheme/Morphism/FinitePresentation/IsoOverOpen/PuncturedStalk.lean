module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing

/-!
# Base change to a punctured local scheme

This file defines the pullback functor from finite-presentation morphisms that are isomorphisms
away from a closed point to the corresponding category over the punctured spectrum of its local
ring.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The punctured local open at a closed point is contained in the inverse image of the
complement of that point. -/
theorem puncturedLocalBaseChange_open_le
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ) :
    V ≤ (S.fromSpecStalk s) ⁻¹ᵁ U := sorry

/-- Base change to the local scheme at a closed point, restricted to morphisms that are
isomorphisms over the corresponding punctured opens. -/
noncomputable abbrev puncturedLocalBaseChange
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ) :
    FinitePresentationIsoOverOpen U ⥤ FinitePresentationIsoOverOpen V :=
  FinitePresentationIsoOverOpen.baseChangeRestrict
    (S.fromSpecStalk s) U
    (puncturedLocalBaseChange_open_le S s hs U hU hUqc V hV)

/-- Base change to the local scheme at a closed point is an equivalence between
finite-presentation morphisms that are isomorphisms away from the point and those that are
isomorphisms over the punctured local scheme. -/
theorem puncturedLocalBaseChange_isEquivalence
    (S : Scheme.{u}) (s : S) (hs : s ∈ closedPoints S)
    (U : S.Opens) (hU : (U : Set S) = ({s} : Set S)ᶜ)
    (hUqc : QuasiCompact U.ι)
    (V : (Spec (CommRingCat.of (S.presheaf.stalk s))).Opens)
    (hV : (V : Set (Spec (CommRingCat.of (S.presheaf.stalk s)))) =
      ({IsLocalRing.closedPoint (S.presheaf.stalk s)} :
        Set (Spec (CommRingCat.of (S.presheaf.stalk s))))ᶜ) :
    Functor.IsEquivalence
      (puncturedLocalBaseChange S s hs U hU hUqc V hV) := sorry

end AlgebraicGeometry
