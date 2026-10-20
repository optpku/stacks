/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedFibres
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.StructureSheaf

/-!
# Structure-sheaf pushforward and geometric fibres

Proper morphisms with reduced and connected geometric fibres have bijective
fibrewise global-sections maps. With flatness and finite presentation, their
canonical structure-sheaf pushforward maps are isomorphisms universally.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- If `f` is proper and has reduced and connected geometric fibres, then the
canonical ground-field map to the global sections of every field-valued fibre
is bijective. -/
theorem fiberGlobalSectionsBijective_of_reducedConnectedGeometricFibres
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [HasReducedGeometricFibres f]
    [AlgebraicSpace.HasConnectedGeometricFibres f] :
    fiberGlobalSectionsBijective f := sorry

/-- If `f` is proper, flat, and of finite presentation, and the geometric fibres of
`f` are reduced and connected, then the canonical map `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism. -/
instance structureSheafMap_isIso_of_reducedConnectedGeometricFibres
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f] :
    IsIso (structureSheafMap f) := sorry

/-- If `f` is proper, flat, and of finite presentation, and its geometric fibres
are reduced and connected, then the canonical structure-sheaf pushforward map
is an isomorphism after every base change `g : Y' ⟶ Y`. -/
instance baseChange_structureSheafMap_isIso_of_reducedConnectedGeometricFibres
    {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f]
    (g : Y' ⟶ Y) :
    IsIso (structureSheafMap (pullback.snd f g)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
