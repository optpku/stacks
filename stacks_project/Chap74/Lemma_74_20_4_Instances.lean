module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap74.Definition_74_20_1_SmoothLocal

/-!
# Smooth locality on source-and-target from source/target locality

A morphism property of algebraic spaces over a scheme `S` that is smooth local
on the source, smooth local on the target, and stable under postcomposition with
smooth morphisms is smooth local on the source-and-target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget

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
