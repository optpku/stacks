/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType

/-!
# Operations on finite-presentation scheme morphisms

This module collects the closure operations for the project-level
`Scheme.Hom.FinitePresentation` class.  They package the corresponding mathlib local property
together with quasi-compactness and quasi-separatedness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The base change of a locally finitely presented scheme morphism is locally finitely
presented. -/
theorem locallyOfFinitePresentation_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : LocallyOfFinitePresentation f) :
    LocallyOfFinitePresentation (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- Finite-presentation scheme morphisms form a morphism property stable under composition. -/
instance finitePresentation_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @FinitePresentation where
  comp_mem f g hf hg :=
    { toLocallyOfFinitePresentation :=
        MorphismProperty.comp_mem _ f g hf.toLocallyOfFinitePresentation
          hg.toLocallyOfFinitePresentation
      toQuasiCompact := MorphismProperty.comp_mem _ f g hf.toQuasiCompact hg.toQuasiCompact
      toQuasiSeparated := MorphismProperty.comp_mem _ f g hf.toQuasiSeparated hg.toQuasiSeparated }

/-- the composite of two finite-presentation scheme morphisms is of finite
presentation. -/
@[stacks 01TR]
theorem FinitePresentation.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : FinitePresentation f) (hg : FinitePresentation g) :
    FinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/-- Finite-presentation scheme morphisms are closed under composition. -/
@[stacks 01TR, instance]
instance finitePresentation_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FinitePresentation f] [FinitePresentation g] :
    FinitePresentation (f ≫ g) :=
  FinitePresentation.comp inferInstance inferInstance

/-- Finite-presentation scheme morphisms form a morphism property stable under base change. -/
instance finitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @FinitePresentation where
  of_isPullback sq hg :=
    { toLocallyOfFinitePresentation :=
        MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq
          hg.toLocallyOfFinitePresentation
      toQuasiCompact :=
        MorphismProperty.of_isPullback (P := @QuasiCompact) sq hg.toQuasiCompact
      toQuasiSeparated :=
        MorphismProperty.of_isPullback (P := @QuasiSeparated) sq hg.toQuasiSeparated }

/-- The left pullback projection is of finite presentation when the right morphism is of finite
presentation. -/
theorem FinitePresentation.pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) {g : S' ⟶ S}
    (hg : FinitePresentation g) :
    FinitePresentation (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

/-- Pulling a finite-presentation right morphism back along an arbitrary morphism gives a
finite-presentation left projection. -/
instance finitePresentation_pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [FinitePresentation g] :
    FinitePresentation (pullback.fst f g) :=
  FinitePresentation.pullback_fst f inferInstance

/-- A finite-presentation scheme morphism remains of finite presentation after base change. -/
theorem FinitePresentation.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : FinitePresentation f) (g : S' ⟶ S) :
    FinitePresentation (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- every base change of a finite-presentation scheme morphism is of finite
presentation. -/
@[stacks 01TS]
theorem finitePresentation_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : FinitePresentation f) :
    FinitePresentation (pullback.snd f g) :=
  hf.pullback_snd g

/-- The pullback projection obtained by base changing a finite-presentation morphism is of finite
presentation. -/
@[stacks 01TS, instance]
instance instFinitePresentationPullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [FinitePresentation f] :
    FinitePresentation (pullback.snd f g) :=
  FinitePresentation.pullback_snd inferInstance g

end AlgebraicGeometry.Scheme.Hom
