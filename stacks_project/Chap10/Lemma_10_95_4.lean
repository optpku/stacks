/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.CountablyGenerated.BaseChange.Submodule
import StacksCheckRecall

/-!
# Countably generated submodules after base change

@stack 05A7
-/

@[expose] public section

universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Lemma 10.95.4 (05A7): every countably generated submodule of `S ⊗[R] M` is contained in
the scalar extension of a countably generated submodule of `M`. -/
@[stacks 05A7]
#check (Submodule.CountablyGenerated.exists_le_baseChange
  (R := R) (S := S) (M := M) :
    ∀ {Q : Submodule S (S ⊗[R] M)}, Q.CountablyGenerated →
      ∃ P : Submodule R M, P.CountablyGenerated ∧ Q ≤ P.baseChange S)

end

#check @TensorProduct.exists_finset_right_span
#check @TensorProduct.exists_countablyGenerated_right
#check @Submodule.CountablyGenerated.baseChange
#check @Submodule.CountablyGenerated.exists_le_baseChange
