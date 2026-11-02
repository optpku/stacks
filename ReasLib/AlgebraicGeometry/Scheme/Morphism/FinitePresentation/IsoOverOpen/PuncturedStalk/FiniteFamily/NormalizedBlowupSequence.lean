/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FiniteNormalizedSequenceSupport

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Realization by a finite absolute normalized point-blowup sequence supported over `T`.
The terminal scheme may vary, and the endpoint is compared in the slice category. -/
def IsNormalizedBlowupSequenceOver {X S : Scheme.{u}} (f : X ⟶ S) (T : Set S) : Prop :=
  ∃ (Z : Scheme.{u}) (q : Scheme.NormalizedBlowupSequence S Z),
    Nonempty (Over.mk q.toSource ≅ Over.mk f) ∧ q.EveryCenterOver T

/-- Sequence realization depends only on the isomorphism class over the base. -/
theorem isNormalizedBlowupSequenceOver_iff_of_iso {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (e : Over.mk f ≅ Over.mk g) (T : Set S) :
    f.IsNormalizedBlowupSequenceOver T ↔ g.IsNormalizedBlowupSequenceOver T := by
  constructor
  · rintro ⟨Z, q, ⟨h⟩, hq⟩
    exact ⟨Z, q, ⟨h ≪≫ e⟩, hq⟩
  · rintro ⟨Z, q, ⟨h⟩, hq⟩
    exact ⟨Z, q, ⟨h ≪≫ e.symm⟩, hq⟩

/-- With no allowed centers, realization is precisely a slice isomorphism to the identity.
This includes zero-length sequences and does not require a nonempty marked family. -/
theorem isNormalizedBlowupSequenceOver_empty_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    f.IsNormalizedBlowupSequenceOver ∅ ↔ Nonempty (Over.mk (𝟙 S) ≅ Over.mk f) := by
  constructor
  · rintro ⟨Z, q, he, hq⟩
    cases q with
    | nil => exact he
    | cons _ _ => exact False.elim hq.1
  · intro he
    exact ⟨S, .nil S, he, trivial⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/-- Normal-base form of the normalized point-blowup locality statement: realization is
invariant under slice isomorphism and can be checked at the marked stalks.

The steps use the existing *absolute* normalization. Normality of `S` ensures that a step
at one marked fiber induces an isomorphism at every other, unselected coordinate. Each
subsequent stage is normal as well. No Noetherian, Nagata, or excellence hypothesis is used.

Source discrepancy (Stacks 0BFZ): the printed statement assumes only finitely many
irreducible components on quasi-compact opens. That generality is false for absolute
normalization, even if the complement is normal. For example, take the disjoint union of
a smooth affine surface and a cusp curve, mark the surface origin and the cusp, and blow up
only the surface origin while leaving the cusp unchanged. The local objects admit a
one-step sequence and an empty sequence, respectively; a nonempty global normalized
sequence has normal terminal scheme and cannot realize this object. Thus `hS_normal` is
an explicit correction to the source, not a consequence of its stated assumptions. -/
theorem existsNormalizedBlowupSequence_iff
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens S]
    (hS_normal : S.isNormal)
    (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X ≅ Y) :
    X.obj.hom.IsNormalizedBlowupSequenceOver (Set.range s) ↔
      ∀ i, (Y i).obj.hom.IsNormalizedBlowupSequenceOver
        ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} : Set _) := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
