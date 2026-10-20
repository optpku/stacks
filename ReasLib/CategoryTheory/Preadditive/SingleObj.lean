/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring homomorphisms as additive functors

A ring homomorphism induces a functor between the corresponding one-object preadditive
categories.  Its map on the unique Hom group is the original ring homomorphism, so the functor is
additive and can be bundled as an `AdditiveFunctor`.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace RingHom

variable {R : Type u} {A : Type v} [Ring R] [Ring A]

/-- The one-object functor induced by a ring homomorphism is additive. -/
instance toFunctor_additive (f : R →+* A) :
    f.toMonoidHom.toFunctor.Additive := sorry
/- Proof strategy: unfold `Functor.Additive`; on the unique Hom group the functor map is `f`, so
the required equality is `f.map_add`. -/

/-- Remark 4.27.3 (5) (Stacks 0BM1): the bundled additive functor between one-object
preadditive categories induced by a ring homomorphism. -/
@[stacks 0BM1 "ring homomorphisms induce additive one-object functors"]
def toAdditiveFunctor (f : R →+* A) : SingleObj R ⥤+ SingleObj A :=
  AdditiveFunctor.of f.toMonoidHom.toFunctor

end RingHom
