/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) [A.HasTotal (up ℤ)]

/- Definition 12.18.3 [012Z]: the simple complex of a cohomological double complex is mathlib's
canonical coproduct total complex. -/
@[stacks 012Z]
#check (A.total (up ℤ) : CochainComplex C ℤ)

/- The existence condition, summand inclusions, and total differential formula remain available
directly from the owner namespace. -/
#check (inferInstance : A.HasTotal (up ℤ))
#check @HomologicalComplex₂.ιTotal
#check @HomologicalComplex₂.total_d
