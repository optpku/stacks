/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Homological.Opposite
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.2

Representable covariant Hom is homological in Mathlib.  The reusable
opposite-category bridge in ReasLib expresses the contravariant statement in
the same canonical `Functor.IsHomological` language.
-/

namespace CategoryTheory

open Limits Opposite
open scoped Pretriangulated.Opposite

universe v u

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (W : D)

@[stacks 0149] #check (inferInstance : (preadditiveCoyoneda.obj (op W)).IsHomological)

@[stacks 0149] #check (inferInstance : (preadditiveYoneda.obj W).rightOp.IsHomological)

end CategoryTheory
