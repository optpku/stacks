/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequenceSupport

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Realization by a finite point-blowup sequence supported over `T`.
The terminal scheme may vary, and the endpoint is compared in the slice category. -/
def IsPointBlowupSequenceOver {X S : Scheme.{u}} (f : X ⟶ S) (T : Set S) : Prop :=
  ∃ (Z : Scheme.{u}) (q : Scheme.PointBlowupSequence S Z),
    Nonempty (Over.mk q.toSource ≅ Over.mk f) ∧ q.EveryCenterOver T

/-- Sequence realization depends only on the isomorphism class over the base. -/
theorem isPointBlowupSequenceOver_iff_of_iso {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (e : Over.mk f ≅ Over.mk g) (T : Set S) :
    f.IsPointBlowupSequenceOver T ↔ g.IsPointBlowupSequenceOver T := by
  constructor
  · rintro ⟨Z, q, ⟨h⟩, hq⟩
    exact ⟨Z, q, ⟨h ≪≫ e⟩, hq⟩
  · rintro ⟨Z, q, ⟨h⟩, hq⟩
    exact ⟨Z, q, ⟨h ≪≫ e.symm⟩, hq⟩

/-- With no allowed centers, realization is precisely a slice isomorphism to the identity.
This includes zero-length sequences and does not require a nonempty marked family. -/
theorem isPointBlowupSequenceOver_empty_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    f.IsPointBlowupSequenceOver ∅ ↔ Nonempty (Over.mk (𝟙 S) ≅ Over.mk f) := by
  constructor
  · rintro ⟨Z, q, he, hq⟩
    cases q with
    | nil => exact he
    | cons _ _ _ _ => exact False.elim hq.1
  · intro he
    exact ⟨S, .nil S, he, trivial⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/-- Under punctured-stalk base change at a finite family of distinct closed points with
quasi-compact open complement, point-blowup sequence realization is equivalent to realization
of every corresponding local object. Endpoints are compared up to isomorphism over the base;
in particular an empty sequence realizes every object isomorphic to the identity. There is
no finite-presentation requirement on intermediate blowups or their reduced point centers. -/
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
    X.obj.hom.IsPointBlowupSequenceOver (Set.range s) ↔
      ∀ i, (Y i).obj.hom.IsPointBlowupSequenceOver
        ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} : Set _) := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
