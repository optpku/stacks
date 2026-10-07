module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

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

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 99.5.8: let `i : X ⟶ X'`, `f : X ⟶ T`, `f' : X' ⟶ T'`, and
`t : T ⟶ T'` form a cartesian square of algebraic spaces, where `t` is a
first-order thickening. Let `F'` be an `𝒪_{X'}`-module flat over `T'`, and set
`F = (pullback i).obj F'`. Then the following are equivalent: `F'` is a
quasi-coherent `𝒪_{X'}`-module of finite presentation; `F'` is an `𝒪_{X'}`-module
of finite presentation; `F` is a quasi-coherent `𝒪_X`-module of finite
presentation; and `F` is an `𝒪_X`-module of finite presentation. -/
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

/-- Finite presentation of `F'` is equivalent to finite presentation of
`(pullback i).obj F'` in a cartesian first-order thickening square, when `F'` is
flat over `T'`. -/
theorem isFinitePresentation_iff_pullback {S : Scheme.{u}}
    {X X' T T' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T')
    (t : T ⟶ T') [IsFirstOrderThickening t] (hcart : IsPullback i f f' t)
    (F' : X'.Modules) (hflat : flatOver F' f') :
    F'.IsFinitePresentation ↔ ((pullback i).obj F').IsFinitePresentation :=
  sorry

/-- Finite presentation of `(pullback i).obj F'` implies finite presentation of
`F'` when `F'` is flat over `T'` in a cartesian first-order thickening square. -/
theorem isFinitePresentation_of_pullback {S : Scheme.{u}}
    {X X' T T' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T')
    (t : T ⟶ T') [IsFirstOrderThickening t] (hcart : IsPullback i f f' t)
    (F' : X'.Modules) (hflat : flatOver F' f')
    [((pullback i).obj F').IsFinitePresentation] :
    F'.IsFinitePresentation :=
  sorry

/-- Finite presentation of `F'` implies finite presentation of
`(pullback i).obj F'` when `F'` is flat over `T'` in a cartesian first-order
thickening square. -/
theorem isFinitePresentation_pullback {S : Scheme.{u}}
    {X X' T T' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T')
    (t : T ⟶ T') [IsFirstOrderThickening t] (hcart : IsPullback i f f' t)
    (F' : X'.Modules) (hflat : flatOver F' f') [F'.IsFinitePresentation] :
    ((pullback i).obj F').IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
