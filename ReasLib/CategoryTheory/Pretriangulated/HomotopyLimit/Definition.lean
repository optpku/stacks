/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.ProductCone
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Homotopy Limits

This leaf owns the presentation-independent predicate that an object is a
homotopy limit of a sequential inverse system. The product is quantified as an
explicit `LimitCone`, so the predicate does not depend on a selected
`HasProduct` instance.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.HomotopyLimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- `X` is a homotopy limit of the sequential inverse system `K` when some
explicit product cone of its terms occurs in a distinguished Milnor triangle with first
vertex `X`. -/
@[stacks 08TC]
def IsOf (K : SequentialInverseSystem D) (X : D) : Prop :=
  ∃ (P : LimitCone (Discrete.functor K.family)) (inclusion : X ⟶ P.cone.pt)
      (connecting : P.cone.pt ⟶ X⟦(1 : ℤ)⟧),
    Triangle.mk inclusion
      (SequentialInverseSystem.Milnor.ProductCone.difference K P) connecting ∈ distTriang D

end CategoryTheory.HomotopyLimit
