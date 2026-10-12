/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Forgetful functors and filtered colimits of commutative algebras

The forgetful functors from commutative algebras to commutative rings and to types preserve
filtered colimits whose indexing universe is bounded by the algebra universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CommAlgCat.FilteredColimits

variable {k : Type u} [CommRing k]

namespace forget₂CommRing

/-- Forgetting a commutative `k`-algebra to a commutative ring preserves filtered colimits of the
specified size. -/
noncomputable instance preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{v, v}
      (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) := sorry

end forget₂CommRing

namespace forgetToType

/-- Forgetting a commutative `k`-algebra to its carrier type preserves filtered colimits whose
index universe is bounded by the algebra universe. -/
noncomputable instance preservesFilteredColimitsOfSize [UnivLE.{v, u}] :
    PreservesFilteredColimitsOfSize.{v, v}
      (forget (CommAlgCat.{u} k)) := sorry

end forgetToType

end CommAlgCat.FilteredColimits
