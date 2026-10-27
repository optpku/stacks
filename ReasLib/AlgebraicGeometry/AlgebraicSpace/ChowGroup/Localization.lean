/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Subspace

/-!
# Localization of Chow groups on algebraic spaces

Fixed-degree Chow maps associated to an open subspace and its reduced closed
complement, packaged as a short complex of abelian groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.ChowLocalization

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (U : OpenSubspace X) (k : ℤ)

/-- Pushforward from the reduced closed complement carries rational boundaries
to rational boundaries. -/
theorem closedPushforward_mem_boundaries :
    U.reducedComplement.boundaries f δ k ≤
      (RationalEquivalence.boundaries f δ k).comap
        (Localization.closedPushforward f δ U k) :=
  sorry

/-- Open restriction carries rational boundaries to rational boundaries. -/
theorem openPullback_mem_boundaries :
    RationalEquivalence.boundaries f δ k ≤
      (U.boundaries f δ k).comap
        (Localization.openPullback f δ U k) :=
  sorry

/-- Pushforward of degree-`k` Chow classes along the reduced-complement closed
immersion. -/
noncomputable def closedPushforward :
    U.reducedComplement.chowGroup f δ k →+ Hom.chowGroup f δ k :=
  QuotientAddGroup.map
    (U.reducedComplement.boundaries f δ k)
    (RationalEquivalence.boundaries f δ k)
    (Localization.closedPushforward f δ U k)
    (closedPushforward_mem_boundaries f δ U k)

/-- Restriction of degree-`k` Chow classes along the open immersion `U.ι`. -/
noncomputable def openPullback :
    Hom.chowGroup f δ k →+ U.chowGroup f δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries f δ k)
    (U.boundaries f δ k)
    (Localization.openPullback f δ U k)
    (openPullback_mem_boundaries f δ U k)

/-- Closed-complement pushforward on a Chow class is induced by cycle
pushforward. -/
theorem closedPushforward_chowMk
    (γ : U.reducedComplement.cycleGroup f δ k) :
    closedPushforward f δ U k (U.reducedComplement.chowMk f δ k γ) =
      Hom.chowMk f δ k (Localization.closedPushforward f δ U k γ) :=
  rfl

/-- Open restriction on a Chow class is induced by cycle restriction. -/
theorem openPullback_chowMk (α : Hom.cycleGroup f δ k) :
    openPullback f δ U k (Hom.chowMk f δ k α) =
      U.chowMk f δ k (Localization.openPullback f δ U k α) :=
  rfl

/-- Closed-complement pushforward followed by open restriction is zero on Chow
groups. -/
theorem closedPushforward_comp_openPullback :
    AddCommGrpCat.ofHom (closedPushforward f δ U k) ≫
      AddCommGrpCat.ofHom (openPullback f δ U k) = 0 :=
  sorry

/-- The localization short complex of degree-`k` Chow groups associated to an
open subspace and its reduced closed complement. -/
noncomputable def complex : ShortComplex Ab.{u + 1} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (closedPushforward f δ U k))
    (AddCommGrpCat.ofHom (openPullback f δ U k))
    (closedPushforward_comp_openPullback f δ U k)

/-- The first arrow of the Chow localization complex is reduced-complement
pushforward. -/
theorem complex_f :
    (complex f δ U k).f = AddCommGrpCat.ofHom (closedPushforward f δ U k) :=
  rfl

/-- The second arrow of the Chow localization complex is open restriction. -/
theorem complex_g :
    (complex f δ U k).g = AddCommGrpCat.ofHom (openPullback f δ U k) :=
  rfl

/-- Restriction from the ambient Chow group to the Chow group of an open
subspace is surjective. -/
theorem openPullback_surjective : Function.Surjective (openPullback f δ U k) :=
  sorry

/-- If two cycles become rationally equivalent on an open subspace, their
difference modulo rational equivalence is pushed forward from a cycle on the
reduced closed complement. -/
theorem exists_closedPushforward (α β : Hom.cycleGroup f δ k)
    (h : U.RationallyEquivalent f δ k
      (Localization.openPullback f δ U k α)
      (Localization.openPullback f δ U k β)) :
    ∃ γ : U.reducedComplement.cycleGroup f δ k,
      RationalEquivalence.RationallyEquivalent f δ k α
        (β + Localization.closedPushforward f δ U k γ) :=
  sorry

/-- Closed-complement pushforward and open restriction form an exact sequence
of Chow groups, with surjective restriction to the open subspace. -/
theorem exact :
    (complex f δ U k).Exact ∧ Epi (complex f δ U k).g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.ChowLocalization
