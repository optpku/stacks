/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalCriterion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change of Unramified Morphisms

Unramified and G-unramified morphisms are stable under base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S S' : Scheme.{u}}

/-- Unramified morphisms are stable under arbitrary base change. -/
instance unramified_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @Unramified where
  of_isPullback sq hf :=
    { toFormallyUnramified := MorphismProperty.of_isPullback sq hf.toFormallyUnramified
      toLocallyOfFiniteType := MorphismProperty.of_isPullback sq hf.toLocallyOfFiniteType }

/-- The pullback of an unramified morphism along any morphism is unramified. -/
@[stacks 02GA]
instance unramified_pullback_snd (f : X ⟶ S) [Unramified f] (g : S' ⟶ S) :
    Unramified (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

/-- G-unramified morphisms are stable under arbitrary base change. -/
instance gUnramified_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @GUnramified where
  of_isPullback sq hf :=
    { toFormallyUnramified := MorphismProperty.of_isPullback sq hf.toFormallyUnramified
      toLocallyOfFinitePresentation :=
        MorphismProperty.of_isPullback sq hf.toLocallyOfFinitePresentation }

/-- The pullback of a G-unramified morphism along any morphism is G-unramified. -/
@[stacks 02GA]
instance gUnramified_pullback_snd (f : X ⟶ S) [GUnramified f] (g : S' ⟶ S) :
    GUnramified (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

namespace Scheme.Hom

/-- Unramifiedness at a point is preserved and reflected by arbitrary base change for a locally
finite-type scheme morphism. -/
theorem unramifiedAt_iff_of_pullback_snd
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (x' : (pullback f g : Scheme)) :
    (pullback.snd f g).UnramifiedAt x' ↔
      f.UnramifiedAt ((pullback.fst f g) x') := sorry

/-- The unramified locus of a locally finite-type scheme morphism commutes with arbitrary base
change. -/
@[stacks 0475]
theorem unramifiedAt_locus_pullback_snd
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] :
    {x' : (pullback f g : Scheme) | (pullback.snd f g).UnramifiedAt x'} =
      (pullback.fst f g) ⁻¹' {x : X | f.UnramifiedAt x} := sorry

/-- G-unramifiedness at a point is preserved and reflected by arbitrary base change for a locally
finite-presentation scheme morphism. -/
theorem gUnramifiedAt_iff_of_pullback_snd
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFinitePresentation f]
    (x' : (pullback f g : Scheme)) :
    (pullback.snd f g).GUnramifiedAt x' ↔
      f.GUnramifiedAt ((pullback.fst f g) x') := sorry

/-- The G-unramified locus of a locally finite-presentation scheme morphism commutes with
arbitrary base change. -/
@[stacks 0475]
theorem gUnramifiedAt_locus_pullback_snd
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFinitePresentation f] :
    {x' : (pullback f g : Scheme) | (pullback.snd f g).GUnramifiedAt x'} =
      (pullback.fst f g) ⁻¹' {x : X | f.GUnramifiedAt x} := sorry

end Scheme.Hom

end AlgebraicGeometry
