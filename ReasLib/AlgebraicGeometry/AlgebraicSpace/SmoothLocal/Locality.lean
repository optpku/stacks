/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Precoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal

/-!
# Smooth locality on source-and-target and source/target locality

A morphism property of algebraic spaces over a scheme `S` is smooth local on
source-and-target if and only if it is smooth local on the source, smooth local
on the target, and stable under postcomposition with smooth morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}

/-- A morphism property that is smooth local on source-and-target is local for
smooth covers of the source. -/
instance toIsLocalAtSource [IsSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtSource (precoverage (@Smooth S)) :=
  sorry

/-- A morphism property that is smooth local on source-and-target is local for
smooth covers of the target. -/
instance toIsLocalAtTarget [IsSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtTarget (precoverage (@Smooth S)) :=
  sorry

/-- A morphism property that is smooth local on source-and-target is preserved by
postcomposition with a smooth morphism. -/
instance toRespectsRightSmooth [IsSmoothLocalAtSourceAndTarget P] :
    P.RespectsRight (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- If `f` has a smooth-local-on-source-and-target property and `g` is smooth,
then `f ≫ g` has the property. -/
theorem postcomp [IsSmoothLocalAtSourceAndTarget P] {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : P f) (hg : Smooth g) : P (f ≫ g) :=
  CategoryTheory.MorphismProperty.RespectsRight.postcomp g hg f hf

/-- Smooth locality on the source and on the target, together with stability under
postcomposition with smooth morphisms, implies smooth locality on source-and-target. -/
@[instance 100]
theorem of_isLocalAtSource_isLocalAtTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtSource (precoverage (@Smooth S))]
    [P.IsLocalAtTarget (precoverage (@Smooth S))]
    [P.RespectsRight (@Smooth S : MorphismProperty (AlgebraicSpace S))] :
    IsSmoothLocalAtSourceAndTarget P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget
