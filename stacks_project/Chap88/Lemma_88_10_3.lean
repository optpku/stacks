/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Algebraization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 88.10.3: Let `A` be a Noetherian ring and `I ⊂ A` an ideal. Let `B`
be an object of (88.2.0.2), i.e. `TopologicallyFiniteType I B`. The equivalent
conditions of Lemma 88.8.2 are also equivalent to the existence of a finite
type `A`-algebra `C` such that `IsEtaleOverComplement I C` (so
`Spec(C) → Spec(A)` is étale over `Spec(A) \ V(I)`) and
`Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B)`. This is the
extra TFAE clause (8) for `RigEtale I B`. -/
@[stacks 0AKG] #check (Algebra.RigEtale.iff_exists_finiteType_isEtaleOverComplement :
    ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
      (I : Ideal A) [Algebra.TopologicallyFiniteType I B],
    Algebra.RigEtale I B ↔
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
        (_ : Algebra.FiniteType A C),
        Algebra.IsEtaleOverComplement I C ∧
          Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B))
