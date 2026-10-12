/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IsAlgClosed.Cardinality
public import ReasLib.FieldTheory.Normal.Embeddings

/-!
# Conjugating field embeddings in algebraically closed extensions

This module constructs a common algebraically closed overfield in which two embeddings of a
field become conjugate by an automorphism.
-/

@[expose] public section

universe u

namespace Field

/-- Two embeddings of a field into another field become conjugate after embedding the target
into a common algebraically closed overfield. -/
theorem exists_algClosed_extension_conjugating_embeddings
    {k L : Type u} [Field k] [Field L] (s t : k →+* L) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (σ : L →+* K) (τ : K ≃+* K),
        σ.comp t = τ.toRingHom.comp (σ.comp s) := sorry

end Field
