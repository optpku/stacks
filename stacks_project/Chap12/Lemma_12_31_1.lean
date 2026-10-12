/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.ShortExact
import StacksCheckRecall

/-!
# Lemma 12.31.1

Compatibility entry point for stagewise exactness of inverse systems. The reusable API is owned
by ReasLib.CategoryTheory.InverseSystem.ShortExact.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex (SequentialInverseSystem C))
variable {i : ℕ} (hS : S.ShortExact)

namespace CategoryTheory

/- Lemma 12.31.1: exactness of a short complex of inverse systems is detected stagewise. -/
@[stacks 02MZ]
#check (SequentialInverseSystem.ShortComplex.exact_iff_exact_app S :
  S.Exact ↔ ∀ i : ℕ, (SequentialInverseSystem.ShortComplex.app S i).Exact)

#check (SequentialInverseSystem.ShortComplex.app S i : ShortComplex C)
#check (SequentialInverseSystem.ShortComplex.ShortExact.app hS :
  (SequentialInverseSystem.ShortComplex.app S i).ShortExact)

end CategoryTheory
