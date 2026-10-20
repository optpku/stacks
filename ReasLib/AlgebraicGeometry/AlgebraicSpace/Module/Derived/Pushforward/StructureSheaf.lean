/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

/-! # Structure-sheaf pushforward along proper flat morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The unbounded derived direct image `Rf_* 𝒪_X` of the structure sheaf. -/
abbrev pushforwardStructureSheafDerived {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y :=
  (Modules.moduleDerivedPushforward f).obj (structureSheafDerived X)

namespace Hom

/-- For a proper, flat, finitely presented morphism whose field-valued fibres have
global sections equal to their base fields, the canonical structure-sheaf map is invertible. -/
theorem structureSheafMap_isIso_of_fiberGlobalSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) :
    IsIso (structureSheafMap f) := sorry

/-- For a proper, flat, finitely presented morphism with bijective fibrewise global-sections
maps, the canonical structure-sheaf map is invertible after every base change. -/
theorem baseChange_structureSheafMap_isIso_of_fiberGlobalSections
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) (g : Y' ⟶ Y) :
    IsIso (structureSheafMap (pullback.snd f g)) := sorry

/-- For a proper, flat, finitely presented morphism with bijective fibrewise global-sections
maps, the canonical map from the structure module to its direct image is invertible. -/
theorem unitToPushforward_isIso_of_fiberGlobalSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) :
    IsIso (IdealSubobject.unitToPushforward f) := sorry

/-- The canonical structure-sheaf map of a proper, flat, finitely presented morphism
is invertible when fibrewise global-sections bijectivity is an active fact. -/
instance structureSheafMap_isIso_of_fact_fiberGlobalSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] [Fact (fiberGlobalSectionsBijective f)] :
    IsIso (structureSheafMap f) :=
  structureSheafMap_isIso_of_fiberGlobalSections f Fact.out

/-- Arbitrary base change preserves invertibility of the canonical structure-sheaf map
when a proper, flat, finitely presented morphism has fibrewise bijectivity as an active fact. -/
instance baseChange_structureSheafMap_isIso_of_fact_fiberGlobalSections
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] [Fact (fiberGlobalSectionsBijective f)]
    (g : Y' ⟶ Y) :
    IsIso (structureSheafMap (pullback.snd f g)) :=
  baseChange_structureSheafMap_isIso_of_fiberGlobalSections f Fact.out g

/-- The structure-module direct-image map of a proper, flat, finitely presented morphism
is invertible when fibrewise global-sections bijectivity is an active fact. -/
instance unitToPushforward_isIso_of_fact_fiberGlobalSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] [Fact (fiberGlobalSectionsBijective f)] :
    IsIso (IdealSubobject.unitToPushforward f) :=
  unitToPushforward_isIso_of_fiberGlobalSections f Fact.out

end Hom

namespace ModuleDerived

/-- For a proper, flat, finitely presented morphism with bijective fibrewise global-sections
maps, its derived structure-sheaf pushforward splits étale locally into the degree-zero
structure sheaf and a perfect complex of Tor-amplitude in `[1, ∞)`. -/
theorem exists_etale_structureSheafPushforward_decomposition
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) (y : Points Y) :
    ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y) (y' : Points Y')
      (hg : AlgebraicSpace.Etale g) (hy : Points.map g y' = y),
      ∃ P : ModuleDerived Y',
        IsPerfect P ∧
          CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeGE (C := Y'.Modules) P 1 ∧
          IsIsomorphic ((pullback g).obj (pushforwardStructureSheafDerived f))
            (structureSheafDerived Y' ⊞ P) := sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
