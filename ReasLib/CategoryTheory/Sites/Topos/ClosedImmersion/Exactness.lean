/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import ReasLib.CategoryTheory.Sites.Topos.ClosedImmersion.Basic

/-!
# Exactness of closed-immersion direct image

The fully-faithful and reflection consequences of an embedding are already
owned by `LeftExactAdjunction.IsEmbedding`. This leaf adds only the three
preservation instances specific to closed immersions.
-/

@[expose] public section

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Direct image along a closed immersion preserves epimorphisms. -/
@[stacks 08M1 "(2)"]
theorem pushforwardPreservesEpimorphisms
    (i : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K) [i.IsClosedImmersion] :
    i.pushforward.PreservesEpimorphisms := sorry

/-- Direct image along a closed immersion preserves coequalizers. -/
@[stacks 08M1 "(3)"]
instance pushforwardPreservesCoequalizers
    (i : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K) [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingParallelPair i.pushforward := sorry

/-- Direct image along a closed immersion preserves pushouts. -/
@[stacks 08M1 "(4)"]
instance pushforwardPreservesPushouts
    (i : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K) [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingSpan i.pushforward := sorry

end CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion
