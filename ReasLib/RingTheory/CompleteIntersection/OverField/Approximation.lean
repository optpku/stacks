/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Algebra.Subalgebra.Directed
public import ReasLib.RingTheory.CompleteIntersection.OverField.AtPrime

/-!
# Complete-intersection approximation of field extensions

This leaf owns the finite-subset and directed-family approximation of an
arbitrary field extension by global complete-intersection subalgebras.
-/

@[expose] public section

namespace IsGlobalCompleteIntersection

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Every finite subset of a field extension lies in a global
complete-intersection subalgebra over the base field. -/
@[stacks 07BV "(1)"]
theorem exists_subalgebra_containing_finset (E : Finset K) :
    ∃ A : Subalgebra k K, IsGlobalCompleteIntersection k A ∧ (E : Set K) ⊆ A := sorry

/-- Every field extension is the directed supremum of a nonempty family of
global complete-intersection subalgebras over the base field. -/
@[stacks 07BV "(1)"]
theorem exists_directed_subalgebra_family :
    ∃ (ι : Type (max u v)) (S : ι → Subalgebra k K), Nonempty ι ∧
      Directed (· ≤ ·) S ∧ (∀ i, IsGlobalCompleteIntersection k (S i)) ∧
        iSup S = (⊤ : Subalgebra k K) := sorry

/-- A finite-type field algebra is a global complete intersection over its
base field. -/
@[stacks 07BV "finite-type field algebras are global complete intersections"]
theorem of_finiteType_field [Algebra.FiniteType k K] :
    IsGlobalCompleteIntersection k K := sorry

end IsGlobalCompleteIntersection
