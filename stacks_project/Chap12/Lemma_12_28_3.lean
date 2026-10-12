/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

section

variable {Ω : Type v}
variable {C : Type u} [Category.{v} C]
variable (P : Ω → C)
variable [HasCoproduct P] [∀ ω, Projective (P ω)]

@[stacks 013D] #check (inferInstance : Projective (∐ P))

end

end CategoryTheory
