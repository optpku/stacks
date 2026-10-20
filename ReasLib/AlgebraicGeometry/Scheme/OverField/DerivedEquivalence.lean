/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Linear
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Two smooth projective schemes over a field are derived equivalent when their perfect
derived categories admit a linear exact equivalence for the structural scalar actions. -/
def derivedEquivalent
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom] : Prop :=
  ∃ F : RingedSpace.ModuleDerived.Perfect (X := X.left.toRingedSpace) ⥤
      RingedSpace.ModuleDerived.Perfect (X := Y.left.toRingedSpace),
    Scheme.ModuleDerived.Perfect.IsLinearFor X.hom Y.hom F ∧
      F.HasTriangulatedStructure ∧ F.IsEquivalence

end AlgebraicGeometry.SchemeOverField
