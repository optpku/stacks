/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Descent of quasi-compact scheme morphisms
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

/-- Quasi-compactness of scheme morphisms descends along morphisms that are surjective and open
on underlying topological spaces. -/
instance descendsAlong_quasiCompact_surjective_inf_isOpenMap :
    DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ topologically @IsOpenMap) := sorry

namespace QuasiCompact

/-- A scheme morphism is quasi-compact if its base change along an open surjective morphism is
quasi-compact. -/
theorem of_isOpenMap_of_surjective_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g]
    (hg_open : IsOpenMap g.base) (hqc : QuasiCompact (pullback.snd f g)) :
    QuasiCompact f := sorry

end QuasiCompact

end AlgebraicGeometry
