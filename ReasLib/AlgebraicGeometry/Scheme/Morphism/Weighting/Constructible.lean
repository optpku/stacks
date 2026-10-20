/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Every integer level set of a weighting of a locally quasi-finite morphism is locally
constructible in the source. -/
theorem IsWeighting.levelSet_isLocallyConstructible {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ}
    (hw : f.IsWeighting w) (n : ℤ) :
    Topology.IsLocallyConstructible {x : X | w x = n} := sorry

/-- Every integer level set of the fibre integral of a weighting of a locally quasi-finite
morphism of finite presentation is locally constructible in the target. -/
theorem IsWeighting.fiberIntegral_levelSet_isLocallyConstructible
    {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f] [FinitePresentation f]
    {w : X → ℤ} (hw : f.IsWeighting w) (n : ℤ) :
    Topology.IsLocallyConstructible
      {y : Y | f.fiberIntegral ⟨f.tendsto_cofinite_cofinite⟩ w y = n} := sorry

end AlgebraicGeometry.Scheme.Hom
