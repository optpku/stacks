/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Localization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Subspace

/-!
# Chow groups of open and closed subspaces

Canonical rational-boundary subgroups, Chow quotients, and quotient maps for
subspaces with their composite structure morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]

/-- The subgroup of rationally trivial cycles on an open subspace. -/
abbrev OpenSubspace.boundaries (U : OpenSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    AddSubgroup (U.cycleGroup f δ k) :=
  @RationalEquivalence.boundaries S B U.X inferInstance inferInstance (U.ι ≫ f)
    (quasiSeparated_openSubspace_comp U f)
    (locallyOfFiniteType_openSubspace_comp U f) δ inferInstance k

/-- The Chow group of an open subspace relative to its composite structure
morphism. -/
abbrev OpenSubspace.chowGroup (U : OpenSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :=
  @Hom.chowGroup S B U.X inferInstance inferInstance (U.ι ≫ f)
    (quasiSeparated_openSubspace_comp U f)
    (locallyOfFiniteType_openSubspace_comp U f) δ inferInstance k

/-- The canonical map from cycles on an open subspace to its Chow group. -/
abbrev OpenSubspace.chowMk (U : OpenSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    U.cycleGroup f δ k →+ U.chowGroup f δ k :=
  @Hom.chowMk S B U.X inferInstance inferInstance (U.ι ≫ f)
    (quasiSeparated_openSubspace_comp U f)
    (locallyOfFiniteType_openSubspace_comp U f) δ inferInstance k

/-- The subgroup of rationally trivial cycles on a closed subspace. -/
abbrev ClosedSubspace.boundaries (W : ClosedSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    AddSubgroup (W.cycleGroup f δ k) :=
  @RationalEquivalence.boundaries S B W.X inferInstance inferInstance (W.ι ≫ f)
    (quasiSeparated_closedSubspace_comp W f)
    (locallyOfFiniteType_closedSubspace_comp W f) δ inferInstance k

/-- The Chow group of a closed subspace relative to its composite structure
morphism. -/
abbrev ClosedSubspace.chowGroup (W : ClosedSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :=
  @Hom.chowGroup S B W.X inferInstance inferInstance (W.ι ≫ f)
    (quasiSeparated_closedSubspace_comp W f)
    (locallyOfFiniteType_closedSubspace_comp W f) δ inferInstance k

/-- The canonical map from cycles on a closed subspace to its Chow group. -/
abbrev ClosedSubspace.chowMk (W : ClosedSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    W.cycleGroup f δ k →+ W.chowGroup f δ k :=
  @Hom.chowMk S B W.X inferInstance inferInstance (W.ι ≫ f)
    (quasiSeparated_closedSubspace_comp W f)
    (locallyOfFiniteType_closedSubspace_comp W f) δ inferInstance k

/-- Two cycles on an open subspace are rationally equivalent when their
difference is a rational boundary for its composite structure morphism. -/
abbrev OpenSubspace.RationallyEquivalent (U : OpenSubspace X) (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (α β : U.cycleGroup f δ k) : Prop :=
  @RationalEquivalence.RationallyEquivalent S B U.X inferInstance inferInstance (U.ι ≫ f)
    (quasiSeparated_openSubspace_comp U f)
    (locallyOfFiniteType_openSubspace_comp U f) δ inferInstance k α β

end AlgebraicGeometry.AlgebraicSpace
