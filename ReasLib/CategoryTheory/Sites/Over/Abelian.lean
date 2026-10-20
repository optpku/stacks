/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Abelian sheaves on slice sites

Inverse image along a change of slice base is exact on abelian sheaves.  The continuous and
cocontinuous direct-image presentations are additive.  These canonical instances let derived
constructions consume the slice functors without rebuilding local additive or exactness evidence.

The exact owner below deliberately takes the exactness instances themselves.  In particular, a
caller may obtain them from a pullback hypothesis, but a source-facing theorem need not expose that
stronger presentation.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- Inverse image along a change of slice base is additive on abelian sheaves. -/
@[stacks 00XY "additivity of slice inverse image", instance]
instance overMapPullback_additive (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) :
    Functor.Additive (J.overMapPullback AddCommGrpCat.{max u v} f) := sorry

/-- Inverse image along a change of slice base preserves finite limits on abelian sheaves. -/
@[stacks 00XY "left exactness of slice inverse image", instance]
instance overMapPullback_preservesFiniteLimits (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteLimits (J.overMapPullback AddCommGrpCat.{max u v} f) := sorry

/-- Inverse image along `f` preserves finite colimits on abelian sheaves. -/
@[stacks 00XY "right exactness of slice inverse image", instance]
instance overMapPullback_preservesFiniteColimits (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteColimits (J.overMapPullback AddCommGrpCat.{max u v} f) := sorry

/-- The exact-functor owner for inverse image along a change of slice base. -/
@[stacks 00XY "exact inverse image on abelian slice sheaves"]
noncomputable abbrev overMapPullbackExact (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) :
    Sheaf (J.over Y) AddCommGrpCat.{max u v} ⥤ₑ
      Sheaf (J.over X) AddCommGrpCat.{max u v} :=
  ExactFunctor.of (J.overMapPullback AddCommGrpCat.{max u v} f)

/-- The continuous direct-image presentation along a change of slice base is additive on abelian
sheaves. -/
@[stacks 00XY "additivity of continuous slice direct image", instance]
instance overMapPushforward_additive (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Functor.Additive (J.overMapPushforward AddCommGrpCat.{max u v} f) := sorry

/-- The cocontinuous direct-image presentation along a change of slice base is additive on abelian
sheaves. -/
@[stacks 00XY "additivity of cocontinuous slice direct image", instance]
instance overMapCocontinuousPushforward_additive (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y)
    [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    Functor.Additive
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (J.over X) (J.over Y)) := sorry

end CategoryTheory.GrothendieckTopology
