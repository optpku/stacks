/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive

/-!
# Excess conormal sheaf of a cartesian square

The excess conormal sheaf of a cartesian square of schemes is the kernel of the
degree-minus-one homology map of naive-cotangent base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace NaiveCotangent.BaseChange

variable {X X' Y Y' : _root_.AlgebraicGeometry.Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical map on degree-minus-one homology induced by naive-cotangent base change
along a cartesian square of schemes. -/
noncomputable def excessConormalMap (hpb : IsPullback g' f' f g) :
    (((_root_.AlgebraicGeometry.Scheme.Modules.pullback g').mapHomologicalComplex (up ℤ)).obj
        (naiveCotangent f)).homology (-1) ⟶
      (naiveCotangent f').homology (-1) :=
  HomologicalComplex.homologyMap (map hpb.toCommSq) (-1)

/-- The excess conormal sheaf of a cartesian square, as the kernel of `excessConormalMap`. -/
noncomputable def excessConormal (hpb : IsPullback g' f' f g) : X'.Modules :=
  kernel (excessConormalMap hpb)

/-- `excessConormalMap` is homology of naive-cotangent base change in degree `-1`. -/
theorem excessConormalMap_eq (hpb : IsPullback g' f' f g) :
    excessConormalMap hpb = HomologicalComplex.homologyMap (map hpb.toCommSq) (-1) := sorry

/-- The excess conormal sheaf is the kernel of `excessConormalMap`. -/
theorem excessConormal_eq (hpb : IsPullback g' f' f g) :
    excessConormal hpb = kernel (excessConormalMap hpb) := sorry

/-- The kernel inclusion of the excess conormal sheaf composes to zero with
`excessConormalMap`. -/
theorem excessConormal_ι_comp_map (hpb : IsPullback g' f' f g) :
    kernel.ι (excessConormalMap hpb) ≫ excessConormalMap hpb = 0 := sorry

/-- Dual of the excess conormal sheaf of a cartesian square. -/
noncomputable def excessConormalDual (hpb : IsPullback g' f' f g) : X'.Modules :=
  Scheme.Modules.dual (excessConormal hpb)

/-- `excessConormalDual` is the module dual of `excessConormal`. -/
theorem excessConormalDual_eq (hpb : IsPullback g' f' f g) :
    excessConormalDual hpb = Scheme.Modules.dual (excessConormal hpb) := sorry

end NaiveCotangent.BaseChange
end AlgebraicGeometry.Scheme.Hom
