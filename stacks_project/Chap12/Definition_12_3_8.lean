/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable (A : Type u) [Category.{v} A]

section

variable [Preadditive A]

/- Definition 12.3.8: once `A` is preadditive, the source condition that `A` be additive is
exactly the canonical limit structure `HasFiniteProducts A`. -/
@[stacks 0104] #check HasFiniteProducts A

section

variable [HasFiniteProducts A]

/- Companion bridge: the source-level direct-sum clause is the upstream owner theorem
`HasFiniteBiproducts.of_hasFiniteProducts`; after installing that canonical instance, the
zero-object owner is the standard derived instance `hasZeroObject_of_hasFiniteBiproducts A`. -/
#check HasFiniteBiproducts.of_hasFiniteProducts
#check hasZeroObject_of_hasFiniteBiproducts

end

end

end CategoryTheory
