/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FinitePresentation.FirstOrderThickening
import StacksCheckRecall

/-!
# Finite presentation across a cartesian first-order thickening of algebraic spaces

In a cartesian square of algebraic spaces whose base morphism is a first-order
thickening, a module on the thickened space that is flat over the thickened base
is finitely presented if and only if its pullback to the special fibre is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 99.5.8: let `i : X ⟶ X'`, `f : X ⟶ T`, `f' : X' ⟶ T'`, and
`t : T ⟶ T'` form a cartesian square of algebraic spaces, where `t` is a
first-order thickening. Let `F'` be an `𝒪_{X'}`-module flat over `T'`, and set
`F = (pullback i).obj F'`. Then the following are equivalent: `F'` is a
quasi-coherent `𝒪_{X'}`-module of finite presentation; `F'` is an `𝒪_{X'}`-module
of finite presentation; `F` is a quasi-coherent `𝒪_X`-module of finite
presentation; and `F` is an `𝒪_X`-module of finite presentation. -/
@[stacks 08W7]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isFinitePresentation_tfae :
    ∀ {S : Scheme.{u}} {X X' T T' : AlgebraicSpace S}
      (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T') (t : T ⟶ T')
      [IsFirstOrderThickening t] (hcart : IsPullback i f f' t)
      (F' : X'.Modules) (hflat : Modules.flatOver F' f'),
    List.TFAE
      [F'.IsQuasicoherent ∧ F'.IsFinitePresentation, F'.IsFinitePresentation,
        ((Modules.pullback i).obj F').IsQuasicoherent ∧
          ((Modules.pullback i).obj F').IsFinitePresentation,
        ((Modules.pullback i).obj F').IsFinitePresentation])
