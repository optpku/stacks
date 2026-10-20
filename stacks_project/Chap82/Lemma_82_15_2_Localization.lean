/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Lemma_82_10_2_Localization

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

section
variable (U : OpenSubspace X)

/-- An open subspace of a good algebraic space remains quasi-separated over the
fixed good base. -/
instance instQuasiSeparated_openSubspace_comp :
    QuasiSeparated (U.ι ≫ f) :=
  sorry

/-- An open subspace of a good algebraic space remains locally of finite type
over the fixed good base. -/
instance instLocallyOfFiniteType_openSubspace_comp :
    LocallyOfFiniteType (U.ι ≫ f) :=
  sorry

/-- The reduced closed complement of an open subspace remains quasi-separated
over the fixed good base. -/
instance instQuasiSeparated_reducedComplement_comp :
    QuasiSeparated (U.reducedComplement.ι ≫ f) :=
  sorry

/-- The reduced closed complement of an open subspace remains locally of finite
type over the fixed good base. -/
instance instLocallyOfFiniteType_reducedComplement_comp :
    LocallyOfFiniteType (U.reducedComplement.ι ≫ f) :=
  sorry

end

variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (U : OpenSubspace X) (k : ℤ)

/-- Pushforward from the reduced closed complement carries rational boundaries
to rational boundaries. -/
theorem closedPushforward_mem_boundaries :
    RationalEquivalence.boundaries (U.reducedComplement.ι ≫ f) δ k ≤
      (RationalEquivalence.boundaries f δ k).comap
        (Localization.closedPushforward f δ U k) :=
  sorry

/-- Open restriction carries rational boundaries to rational boundaries. -/
theorem openPullback_mem_boundaries :
    RationalEquivalence.boundaries f δ k ≤
      (RationalEquivalence.boundaries (U.ι ≫ f) δ k).comap
        (Localization.openPullback f δ U k) :=
  sorry

/-- Pushforward of degree-`k` Chow classes along the reduced-complement closed
immersion. -/
noncomputable def closedPushforward :
    (AlgebraicGeometry.AlgebraicSpace.Hom.chowGroup (U.reducedComplement.ι ≫ f)) δ k →+ (AlgebraicGeometry.AlgebraicSpace.Hom.chowGroup f) δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries (U.reducedComplement.ι ≫ f) δ k)
    (RationalEquivalence.boundaries f δ k)
    (Localization.closedPushforward f δ U k)
    (closedPushforward_mem_boundaries f δ U k)

/-- Restriction of degree-`k` Chow classes along the open immersion `U.ι`. -/
noncomputable def openPullback :
    (AlgebraicGeometry.AlgebraicSpace.Hom.chowGroup f) δ k →+ (AlgebraicGeometry.AlgebraicSpace.Hom.chowGroup (U.ι ≫ f)) δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries f δ k)
    (RationalEquivalence.boundaries (U.ι ≫ f) δ k)
    (Localization.openPullback f δ U k)
    (openPullback_mem_boundaries f δ U k)

/-- Closed-complement pushforward on a Chow class is induced by cycle
pushforward. -/
theorem closedPushforward_chowMk
    (γ : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k) :
    closedPushforward f δ U k ((AlgebraicGeometry.AlgebraicSpace.Hom.chowMk (U.reducedComplement.ι ≫ f)) δ k γ) =
      (AlgebraicGeometry.AlgebraicSpace.Hom.chowMk f) δ k (Localization.closedPushforward f δ U k γ) :=
  sorry

/-- Open restriction on a Chow class is induced by cycle restriction. -/
theorem openPullback_chowMk (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) :
    openPullback f δ U k ((AlgebraicGeometry.AlgebraicSpace.Hom.chowMk f) δ k α) =
      (AlgebraicGeometry.AlgebraicSpace.Hom.chowMk (U.ι ≫ f)) δ k (Localization.openPullback f δ U k α) :=
  sorry

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
  sorry

/-- The second arrow of the Chow localization complex is open restriction. -/
theorem complex_g :
    (complex f δ U k).g = AddCommGrpCat.ofHom (openPullback f δ U k) :=
  sorry

/-- Open restriction is canonically an epimorphism on Chow groups. -/
instance openPullback_epi : Epi (complex f δ U k).g :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hom.ChowLocalization
