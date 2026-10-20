/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Finite presentation across a cartesian first-order thickening of algebraic spaces

In a cartesian square of algebraic spaces whose base morphism is a first-order
thickening, a module on the thickened space that is flat over the thickened base
is finitely presented if and only if its pullback is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Finite presentation of a module is equivalent to finite presentation of its
pullback in a cartesian first-order thickening square, when the module is flat
over the thickened base. -/
theorem isFinitePresentation_iff_pullback {S : Scheme.{u}}
    {X X' T T' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T')
    (t : T ⟶ T') [IsFirstOrderThickening t] (hcart : IsPullback i f f' t)
    (F' : X'.Modules) (hflat : flatOver F' f') :
    F'.IsFinitePresentation ↔ ((pullback i).obj F').IsFinitePresentation :=
  sorry

/-- In a cartesian square over a first-order thickening, a module flat over the
thickened base is finitely presented exactly when its pullback is finitely
presented. On either space this is also equivalent to being quasi-coherent and
finitely presented. -/
@[stacks 08W7]
theorem isFinitePresentation_tfae {S : Scheme.{u}} {X X' T T' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T') (t : T ⟶ T')
    [IsFirstOrderThickening t] (hcart : IsPullback i f f' t)
    (F' : X'.Modules) (hflat : flatOver F' f') :
    List.TFAE
      [F'.IsQuasicoherent ∧ F'.IsFinitePresentation, F'.IsFinitePresentation,
        ((pullback i).obj F').IsQuasicoherent ∧ ((pullback i).obj F').IsFinitePresentation,
        ((pullback i).obj F').IsFinitePresentation] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
