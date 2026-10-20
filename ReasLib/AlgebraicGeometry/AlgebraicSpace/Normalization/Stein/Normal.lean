/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.GenericFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-!
# Proper morphisms towards normal integral algebraic spaces

The canonical global-sections map on the generic fibre detects when a proper
morphism to a normal integral algebraic space has trivial structure-sheaf direct
image and geometrically connected fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A proper morphism from a reduced algebraic space to an integral normal algebraic
space induces an isomorphism on the structure-sheaf direct image and has geometrically
connected fibres if all source generic points map to the target generic point and
the canonical map from its residue field to the generic fibre's global sections is
an isomorphism. -/
theorem structureSheaf_and_connectedFibres
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [IsIntegral Y] [IsNormal Y] [IsReduced X]
    {ξ : Points Y} (hξ : ξ ∈ genericPoints Y)
    (h_generic : ∀ ⦃x : Points X⦄, x ∈ genericPoints X → Points.map f x = ξ)
    (hΓ : IsIso (genericFiberGlobalSectionsMap f ξ)) :
    IsIso (AlgebraicGeometry.AlgebraicSpace.commStructureSheafMap f) ∧
      AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
