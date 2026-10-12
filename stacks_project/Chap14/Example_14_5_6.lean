/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import StacksCheckRecall

/-!
@stack 0B13
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

variable (n : ℕ)

/- Example 14.5.6: the costandard `n`-simplex is the covariant representable functor on
`SimplexCategory` represented by `⦋n⦌`. -/
@[stacks 0B13]
#check (coyoneda.obj (op ⦋n⦌) : CosimplicialObject (Type))

variable (k : ℕ)

/- Evaluating the costandard simplex represented by `⦋n⦌` at `⦋k⦌` is definitionally the
hom-set `Hom([n], [k])` in `SimplexCategory`, so this should stay a direct check of the owner’s
evaluation formula rather than a second named theorem. -/
#check
  (rfl :
    (coyoneda.obj (op ⦋n⦌) : CosimplicialObject (Type)) ^⦋k⦌ = (⦋n⦌ ⟶ ⦋k⦌))
