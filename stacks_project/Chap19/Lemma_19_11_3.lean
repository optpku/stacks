/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ShortComplex.SubobjectCardinal
import StacksCheckRecall

@[expose] public section

/-!
# Subobject Cardinals in a Short Exact Sequence

The reusable monomorphism, epimorphism, and short-exact-sequence API is owned by ReasLib. This
file records the two source clauses as typed checks.
-/

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} (hS : S.ShortExact)

/- Lemma 19.11.3 (1): `Subobject S.X₁` has cardinality at most `Subobject S.X₂`. -/
@[stacks 079D "(1)"] #check
  (ShortComplex.ShortExact.subobjectCardinal_f_le hS :
    Cardinal.mk (Subobject S.X₁) ≤ Cardinal.mk (Subobject S.X₂))

/- Lemma 19.11.3 (2): `Subobject S.X₃` has cardinality at most `Subobject S.X₂`. -/
@[stacks 079D "(2)"] #check
  (ShortComplex.ShortExact.subobjectCardinal_g_le hS :
    Cardinal.mk (Subobject S.X₃) ≤ Cardinal.mk (Subobject S.X₂))

end CategoryTheory
