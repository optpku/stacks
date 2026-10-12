/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import ReasLib.CategoryTheory.Adjunction.Linear
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear right internal Hom functors

The target-variable functor of a chosen right internal Hom is linear because it is right adjoint
to linear tensoring by its fixed source object.
-/

@[expose] public section

universe w u v

namespace CategoryTheory.RightInternalHom

open Opposite

variable {k : Type w} [Semiring k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
variable [MonoidalCategory C]

/-- The target-variable functor of a chosen right internal Hom is `k`-linear. -/
@[stacks 0GWJ "linear right internal-Hom functor"]
instance homObjLinear [MonoidalPreadditive C] [MonoidalLinear k C]
    (H : RightInternalHom C) (X : C) :
    Functor.Linear k (H.hom.obj (op X)) :=
  (H.adj₂.adj X).right_adjoint_linear

variable [MonoidalPreadditive C] [MonoidalLinear k C]
variable (H : RightInternalHom C) (X : C)

#synth Functor.Linear k (H.hom.obj (op X))

end CategoryTheory.RightInternalHom
