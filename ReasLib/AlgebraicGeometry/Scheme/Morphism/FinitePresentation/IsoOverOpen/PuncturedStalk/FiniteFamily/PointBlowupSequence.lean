/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequenceSupport

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/-- Under punctured-stalk base change at a finite family of distinct closed points with
quasi-compact open complement, a finite-presentation morphism that is an isomorphism over
the complement factors as a finite sequence of point blowups over the family exactly when
every corresponding local morphism factors as a finite sequence of point blowups over its
distinguished closed point. -/
theorem existsPointBlowupSequence_iff
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X ≅ Y) :
    (∃ q : Scheme.PointBlowupSequence S X.obj.left,
      q.toSource = X.obj.hom ∧ q.EveryCenterOver (Set.range s)) ↔
      ∀ i, ∃ q : Scheme.PointBlowupSequence
          (Spec (CommRingCat.of (S.presheaf.stalk (s i)))) (Y i).obj.left,
        q.toSource = (Y i).obj.hom ∧
          q.EveryCenterOver
            ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} : Set _) := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
