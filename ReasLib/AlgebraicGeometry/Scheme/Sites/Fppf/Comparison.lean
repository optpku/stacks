/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every syntomic covering family of schemes is an fppf covering family. -/
theorem bigSyntomicPrecoverage_le_fppfPrecoverage :
    bigSyntomicPrecoverage.{u} ≤ fppfPrecoverage.{u} := sorry

/-- Every smooth covering family of schemes is an fppf covering family. -/
theorem bigSmoothPrecoverage_le_fppfPrecoverage :
    bigSmoothPrecoverage.{u} ≤ fppfPrecoverage.{u} := sorry

/-- Every étale covering family of schemes is an fppf covering family. -/
theorem etalePrecoverage_le_fppfPrecoverage :
    etalePrecoverage.{u} ≤ fppfPrecoverage.{u} := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.StandardTopology

/-- Every standard topology is weaker than the big fppf topology. -/
theorem overTopology_le_fppf (τ : StandardTopology) (S : Scheme.{u}) :
    τ.overTopology S ≤ StandardTopology.fppf.overTopology S := sorry

/-- The identity functor induces a morphism of sites from the big fppf site
to a selected standard site. -/
instance toFppf_isMorphismOfSites (τ : StandardTopology) (S : Scheme.{u}) :
    IsMorphismOfSites (τ.overTopology S) (StandardTopology.fppf.overTopology S)
      (𝟭 (Over S)) := sorry

/-- Pullback along the identity from a standard site to the big fppf site
preserves finite limits. -/
instance toFppfSheafPullback_preservesFiniteLimits
    (τ : StandardTopology) (S : Scheme.{u}) :
    Limits.PreservesFiniteLimits
      ((𝟭 (Over S)).sheafPullback (Type (u + 1))
        (τ.overTopology S) (StandardTopology.fppf.overTopology S)) := sorry

/-- The morphism of topoi from the big fppf site to a selected standard site. -/
def toFppf (τ : StandardTopology) (S : Scheme.{u}) :
    MorphismOfTopoiIn (τ.overTopology S) (StandardTopology.fppf.overTopology S) :=
  (IsMorphismOfSites.toMorphismOfTopoiIn (𝟭 (Over S)) :
    LeftExactAdjunction
      (Sheaf (StandardTopology.fppf.overTopology S) (Type (u + 1)))
      (Sheaf (τ.overTopology S) (Type (u + 1))))

end AlgebraicGeometry.StandardTopology
