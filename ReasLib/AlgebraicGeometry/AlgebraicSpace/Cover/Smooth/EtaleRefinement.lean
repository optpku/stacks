/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.EtaleRefinement

/-!
# Étale refinements of smooth coverings of algebraic spaces

Every smooth covering family of an algebraic space admits an étale covering
that refines it.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.SmoothCovering

/-- Every smooth covering family of an algebraic space over a scheme admits an
étale covering that refines it. -/
@[stacks 0CFV]
theorem exists_etaleRefinement {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {family : ι → Over X} (hfamily : SmoothCovering family) :
    ∃ 𝒱 : (@etalePrecoverage S).ZeroHypercover.{u} X,
      Refines (ofArrows 𝒱.X 𝒱.f)
        (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmoothCovering
