/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Dimension.GenericRank
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u

/- Lemma (0H9Y): An injective extension of domains preserves cardinal module rank.
The scalar extension is written S ⊗[R] M, canonically isomorphic to M ⊗[R] S;
the checked equality has the symmetric orientation of the source statement. -/
@[stacks 0H9Y] #check (Module.rank_baseChange_of_injective :
  ∀ {R : Type u} [CommRing R] [IsDomain R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S],
    Function.Injective (algebraMap R S) →
    ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Module.rank S (S ⊗[R] M) = Module.rank R M)
