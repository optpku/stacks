module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FiberEulerCharacteristic

/-!
# Compatibility for derived-fiber Euler characteristics

The derived-fiber API is provided by its mathematical library owner. The chosen
geometric representative is also available under its historical qualified name.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A chosen geometric point over a point, obtained by algebraic closure of a
field-valued representative. -/
noncomputable abbrev geometricPointOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : GeometricPoint X :=
  AlgebraicGeometry.AlgebraicSpace.geometricPointOver x

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.fiberEulerChar_isLocallyConstant :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X),
    ModuleDerived.IsPerfect E → IsLocallyConstant (ModuleDerived.fiberEulerChar E))
