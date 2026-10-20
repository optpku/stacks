/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Maps.Basic

/-!
# Submersive morphisms of schemes

This module defines submersive scheme morphisms through quotient maps on
underlying topological spaces. The universal condition is expressed through
`MorphismProperty.universally`, together with its composition and base-change
operations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The scheme-morphism property of being a quotient map on underlying topological spaces. -/
abbrev submersiveProperty : MorphismProperty Scheme.{u} :=
  topologically @Topology.IsQuotientMap

/-- Submersive morphisms are closed under composition. -/
instance submersiveProperty_isStableUnderComposition :
    submersiveProperty.IsStableUnderComposition := sorry

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A scheme morphism is submersive when its map of underlying topological spaces is a
quotient map. -/
class Submersive (f : X ⟶ Y) : Prop where
  isQuotientMap : submersiveProperty f

/-- Unfold submersiveness as the quotient-map condition on underlying topological spaces. -/
theorem submersive_iff_base_isQuotientMap :
    Submersive f ↔ Topology.IsQuotientMap f := sorry

attribute [simp] submersive_iff_base_isQuotientMap

/-- A submersive scheme morphism is a quotient map on its underlying topological spaces. -/
theorem Scheme.Hom.isQuotientMap (f : X ⟶ Y) [Submersive f] :
    Topology.IsQuotientMap f := sorry

/-- A scheme morphism is universally submersive when every base change is submersive. -/
class UniversallySubmersive (f : X ⟶ Y) : Prop where
  universally : submersiveProperty.universally f

/-- Unfold universal submersiveness as the universal quotient-map condition on pullbacks. -/
theorem universallySubmersive_iff_universally :
    UniversallySubmersive f ↔ submersiveProperty.universally f := sorry

attribute [simp] universallySubmersive_iff_universally

/-- A universally submersive morphism is submersive. -/
theorem UniversallySubmersive.submersive (hf : UniversallySubmersive f) :
    Submersive f := sorry

/-- Typeclass form of the fact that universally submersive morphisms are submersive. -/
instance instSubmersiveOfUniversallySubmersive [UniversallySubmersive f] :
    Submersive f := sorry

/-- A universally submersive morphism is a quotient map on its underlying topological spaces. -/
theorem UniversallySubmersive.isQuotientMap (hf : UniversallySubmersive f) :
    Topology.IsQuotientMap f := sorry

/-- Every base change of a universally submersive morphism is universally submersive. -/
@[stacks 0CES]
theorem UniversallySubmersive.pullback_snd
    {T : Scheme.{u}} (hf : UniversallySubmersive f) (g : T ⟶ Y) :
    UniversallySubmersive (pullback.snd f g) := sorry

/-- Typeclass form of stability of universal submersiveness under arbitrary base change. -/
instance universallySubmersive_pullback_snd
    {T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) [UniversallySubmersive f] :
    UniversallySubmersive (pullback.snd f g) := sorry

end

/-- Universally submersive scheme morphisms are closed under composition. -/
instance universallySubmersive_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @UniversallySubmersive := sorry

/-- Universally submersive scheme morphisms are stable under arbitrary base change. -/
instance universallySubmersive_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @UniversallySubmersive := sorry

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composite of submersive scheme morphisms is submersive. -/
@[stacks 0CET]
theorem submersive_comp (hf : Submersive f) (hg : Submersive g) :
    Submersive (f ≫ g) := sorry

/-- The composite of universally submersive scheme morphisms is universally submersive. -/
@[stacks 0CET]
theorem universallySubmersive_comp
    (hf : UniversallySubmersive f) (hg : UniversallySubmersive g) :
    UniversallySubmersive (f ≫ g) := sorry

/-- Typeclass form of composition stability for submersive morphisms. -/
instance instSubmersiveComp [Submersive f] [Submersive g] :
    Submersive (f ≫ g) := sorry

/-- Typeclass form of composition stability for universally submersive morphisms. -/
instance instUniversallySubmersiveComp [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) := sorry

end

end AlgebraicGeometry
