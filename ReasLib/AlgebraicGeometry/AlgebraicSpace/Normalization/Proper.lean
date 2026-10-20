/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Proper normalization of algebraic spaces

For a proper morphism of algebraic spaces, the canonical map to the relative
normalization is proper with connected geometric fibres. If the target is
locally Noetherian, the structure morphism of the relative normalization is
finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom

namespace Proper

/-- The canonical map from the source into the relative normalization of a proper
morphism of algebraic spaces is proper. -/

instance toNormalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] : Proper (toNormalization f) :=
  sorry

end Proper

namespace HasConnectedGeometricFibres

/-- The canonical map from the source into the relative normalization of a proper
morphism of algebraic spaces has connected geometric fibres. -/
instance toNormalization_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] :
    HasConnectedGeometricFibres (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a proper
morphism of algebraic spaces to a locally Noetherian target has connected
geometric fibres. -/

theorem toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [IsLocallyNoetherian Y] :
    HasConnectedGeometricFibres (toNormalization f) :=
  sorry

end HasConnectedGeometricFibres

namespace IsFinite

/-- The structure morphism from the relative normalization of a proper morphism
of algebraic spaces to a locally Noetherian target is finite. -/

instance fromNormalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y] :
    IsFinite (fromNormalization f) :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
