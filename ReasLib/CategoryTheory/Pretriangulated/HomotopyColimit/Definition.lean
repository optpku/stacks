/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Sequential.CoproductCocone
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Homotopy Colimits

@stack 090Z

`CategoryTheory.Limits.Sequential.CoproductCocone.telescopeMap` is the neutral
algebraic owner of the telescope endomorphism on an explicitly supplied
coproduct. This leaf adds only the pretriangulated predicate saying that some
such coproduct and distinguished telescope triangle present a sequential
homotopy colimit.
-/

namespace CategoryTheory

open Limits Pretriangulated

universe v u

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

namespace HomotopyColimit

/-- Stacks 090Z, Definition 13.33.1: `X` is a homotopy colimit of a sequential diagram `K`
when an explicitly supplied coproduct of the terms of `K` fits into a distinguished telescope
triangle with third vertex `X`. -/
@[stacks 090Z]
def IsOf (K : ℕ ⥤ D) (X : D) : Prop :=
  ∃ P : ColimitCocone (Discrete.functor K.obj),
    ∃ toCocone : P.cocone.pt ⟶ X,
      ∃ connecting : X ⟶ P.cocone.pt⟦(1 : ℤ)⟧,
        Triangle.mk (Limits.Sequential.CoproductCocone.telescopeMap K P)
          toCocone connecting ∈ distTriang D

end HomotopyColimit

end CategoryTheory
