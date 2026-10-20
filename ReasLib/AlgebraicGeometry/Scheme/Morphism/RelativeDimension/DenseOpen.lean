/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.DenseOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending relative-dimension bounds from a dense open

A relative-dimension bound for a flat morphism locally of finite type extends from a dense
open of the target when the morphism is locally of finite presentation or the open is
retrocompact.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE

/-- A flat morphism locally of finite type has relative dimension at most `e` if it has that
bound over a dense open and either the morphism is locally of finite presentation or the open
is retrocompact. -/
@[stacks 081L]
theorem of_restrict_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFiniteType f] (U : S.Opens) (e : ℕ)
    (hU_dense : Dense (U : Set S)) [RelativeDimensionLE (f ∣_ U) e]
    (h_finitePresentation_or_retrocompact :
      LocallyOfFinitePresentation f ∨ IsRetrocompact (U : Set S)) :
    RelativeDimensionLE f e := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE
