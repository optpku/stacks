/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace AtWorstNodal

/-- The at-worst-nodal source locus is the greatest source open on which the
restriction of a flat, locally finitely presented morphism is at worst nodal. -/
theorem sourceLocus_isGreatest
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    IsGreatest
      {U : X.Opens | AtWorstNodal (U.ι ≫ f)}
      (MorphismProperty.sourceLocus
        (@AtWorstNodal : MorphismProperty Scheme.{u}) f) := sorry

/-- The at-worst-nodal source locus of a flat, locally finitely presented
morphism pulls back to the source locus after arbitrary base change. -/
theorem sourceLocus_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (g : S' ⟶ S) :
    (pullback.fst f g) ⁻¹ᵁ
        (MorphismProperty.sourceLocus
          (@AtWorstNodal : MorphismProperty Scheme.{u}) f) =
      MorphismProperty.sourceLocus
        (@AtWorstNodal : MorphismProperty Scheme.{u}) (pullback.snd f g) := sorry

end AtWorstNodal
end AlgebraicGeometry
