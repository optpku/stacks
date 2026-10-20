/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Topology.Constructible

/-!
# Exactness of pro-étale direct image

The direct image of abelian sheaves on small pro-étale sites preserves finite
limits. For finite morphisms locally of finite presentation it also preserves
finite colimits and is exact.
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {Z X : Scheme.{u}} (f : Z ⟶ X)

/-- The small pro-étale abelian direct image along any scheme morphism preserves
finite limits. -/
instance smallPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (smallPushforward f) := sorry

/-- The small pro-étale abelian direct image along a finite morphism locally of
finite presentation preserves finite colimits. -/
instance smallPushforward_preservesFiniteColimits [IsFinite f] [LocallyOfFinitePresentation f] :
    PreservesFiniteColimits (smallPushforward f) := sorry

/-- The small pro-étale abelian direct image along a finite morphism locally of
finite presentation is exact. -/
theorem smallPushforward_exact [IsFinite f] [LocallyOfFinitePresentation f] :
    exactFunctor (Sheaf (topology Z) AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) (smallPushforward f) :=
  (exactFunctor_iff (smallPushforward f)).2 ⟨inferInstance, inferInstance⟩

/-- The small pro-étale abelian direct image along a closed immersion with
retrocompact complement is exact. -/
theorem smallPushforward_exact_of_isRetrocompact_compl
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (h : IsRetrocompact (Set.range i)ᶜ) :
    exactFunctor (Sheaf (topology Z) AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) (smallPushforward i) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
