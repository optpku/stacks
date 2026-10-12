/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import ReasLib.Algebra.Module.CountablyGenerated.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Countably generated submodules under scalar extension

Countably generated submodules remain countably generated after scalar extension. Conversely, a
countably generated submodule of a scalar extension is contained in the scalar extension of a
countably generated submodule over the base semiring.
-/

universe u v w

open scoped TensorProduct

namespace TensorProduct

variable {R : Type u} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- Every tensor is contained in the scalar extension of the span of finitely many elements of
the right tensor factor. -/
@[stacks 05A7 "finite tensor support"]
theorem exists_finset_right_span (x : S ⊗[R] M) :
    ∃ s : Finset M, x ∈ (Submodule.span R (s : Set M)).baseChange S := sorry

/-- A countable set of tensors is contained in the scalar extension of a countably generated
submodule of the right tensor factor. -/
@[stacks 05A7 "countable tensor support"]
theorem exists_countablyGenerated_right (s : Set (S ⊗[R] M)) (hs : s.Countable) :
    ∃ P : Submodule R M, P.CountablyGenerated ∧ s ⊆ P.baseChange S := sorry

end TensorProduct

namespace Submodule.CountablyGenerated

section Semiring

variable {R : Type u} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- Scalar extension preserves countable generation of submodules. -/
@[stacks 05A8 "countable generation under base change"]
theorem baseChange {P : Submodule R M} (hP : P.CountablyGenerated) :
    (P.baseChange S).CountablyGenerated := sorry

/-- Semiring form of the countable-support descent statement for a submodule of a scalar
extension. -/
@[stacks 05A7 "semiring form"]
theorem exists_le_baseChange {Q : Submodule S (S ⊗[R] M)}
    (hQ : Q.CountablyGenerated) :
    ∃ P : Submodule R M, P.CountablyGenerated ∧ Q ≤ P.baseChange S := sorry

end Semiring

end Submodule.CountablyGenerated
