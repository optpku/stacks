/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Universal homeomorphisms of schemes

This module owns the scheme-morphism property of being a universal homeomorphism.  It is
formulated through the reusable `MorphismProperty.universally` interface, so its pullback and
topological APIs can be used independently of any textbook chapter.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The scheme-morphism property of inducing a homeomorphism on underlying topological spaces. -/
abbrev topologicallyIsHomeomorph : MorphismProperty Scheme.{u} :=
  topologically fun f ↦ IsHomeomorph f

/-- Homeomorphisms on underlying spaces are stable under composition. -/
instance topologicallyIsHomeomorph_isStableUnderComposition :
    topologicallyIsHomeomorph.IsStableUnderComposition :=
  topologically_isStableUnderComposition (fun f ↦ IsHomeomorph f)
    (fun _ _ hf hg ↦ hg.comp hf)

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A scheme morphism is a universal homeomorphism when every base change is a homeomorphism on
underlying topological spaces. -/
@[stacks 04DD]
class UniversalHomeomorphism (f : X ⟶ Y) : Prop where
  universally_isHomeomorph : universally topologicallyIsHomeomorph f

/-- The defining universal topological condition characterizes universal homeomorphisms. -/
@[stacks 04DD]
theorem universalHomeomorphism_iff :
    UniversalHomeomorphism f ↔ universally topologicallyIsHomeomorph f :=
  ⟨fun h ↦ h.universally_isHomeomorph, fun h ↦ ⟨h⟩⟩

/-- Every pullback projection of a universal homeomorphism is a homeomorphism on underlying
topological spaces. -/
@[stacks 04DD]
theorem UniversalHomeomorphism.pullbackSnd_isHomeomorph
    [UniversalHomeomorphism f] {T : Scheme.{u}} (g : T ⟶ Y) :
    IsHomeomorph (pullback.snd f g) :=
  UniversalHomeomorphism.universally_isHomeomorph (f := f)
    (pullback.fst f g) g (pullback.snd f g) (IsPullback.of_hasPullback f g).flip

/-- A universal homeomorphism is a homeomorphism on its underlying topological spaces. -/
@[stacks 04DD]
theorem Scheme.Hom.isHomeomorph (f : X ⟶ Y) [UniversalHomeomorphism f] :
    IsHomeomorph f :=
  universally_le topologicallyIsHomeomorph f
    UniversalHomeomorphism.universally_isHomeomorph

end

/-- Universal homeomorphisms are stable under composition. -/
instance universalHomeomorphism_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @UniversalHomeomorphism where
  comp_mem f g hf hg :=
    ⟨topologicallyIsHomeomorph.universally.comp_mem f g
      hf.universally_isHomeomorph hg.universally_isHomeomorph⟩

/-- The composite of universal homeomorphisms is a universal homeomorphism. -/
theorem UniversalHomeomorphism.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : UniversalHomeomorphism f) (hg : UniversalHomeomorphism g) :
    UniversalHomeomorphism (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/-- Typeclass form of composition stability for universal homeomorphisms. -/
instance universalHomeomorphism_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) :=
  UniversalHomeomorphism.comp inferInstance inferInstance

/-- Universal homeomorphisms are stable under arbitrary base change. -/
instance universalHomeomorphism_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @UniversalHomeomorphism where
  of_isPullback h hf :=
    ⟨topologicallyIsHomeomorph.universally.of_isPullback h hf.universally_isHomeomorph⟩

/-- The pullback projection obtained by base changing a universal homeomorphism
is a universal homeomorphism. -/
theorem UniversalHomeomorphism.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : UniversalHomeomorphism f) (g : S' ⟶ S) :
    UniversalHomeomorphism (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- Typeclass form of base-change stability for universal homeomorphisms. -/
instance universalHomeomorphism_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [UniversalHomeomorphism f] :
    UniversalHomeomorphism (pullback.snd f g) :=
  UniversalHomeomorphism.pullback_snd inferInstance g

end AlgebraicGeometry
