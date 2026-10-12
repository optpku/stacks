/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Preadditive.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable (A : GradedObjectWithShift (1 : ℤ) 𝒜) (k i : ℤ)

/- Definition 12.16.4: the `k`-shift is the canonical shifted object `A⟦k⟧`.  Mathlib uses the
component formula `(A⟦k⟧) i = A (i + k)`; this is the source formula `A (k + i)` in the canonical
additive-group orientation. -/
@[stacks 09MG] #check
  (GradedObject.shiftFunctor_obj_apply (1 : ℤ) A i k :
    (A⟦k⟧) i = A (i + k • (1 : ℤ)))

/- Shifting a morphism uses the same componentwise reindexing. -/
#check @GradedObject.shiftFunctor_map_apply
