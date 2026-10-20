/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.RegularSequence
import StacksCheckRecall

@[expose] public section

open RingTheory.Sequence
open scoped ENat

universe u v

/- Lemma 47.11.3 (1): if `x ∈ I` is a nonzerodivisor on a finite `A`-module
`M` with `IM ≠ M`, then quotienting `M` by `xM` lowers its `I`-depth by one. -/
@[stacks 0BUW] #check
  (Ideal.depth_quotSMulTop_eq_sub_one :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A) (hIM : I • (⊤ : Submodule A M) ≠ ⊤) {x : A}
      (hx : x ∈ I) (hreg : IsSMulRegular M x),
      I.depth (QuotSMulTop x M) = I.depth M - 1)

/- Lemma 47.11.3 (2): every `M`-regular sequence in `I` extends to an
`M`-regular sequence in `I` whose length is the `I`-depth of `M`. -/
@[stacks 0BUW] #check
  (Ideal.exists_isRegular_append_eq_depth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A) (hIM : I • (⊤ : Submodule A M) ≠ ⊤) {rs : List A}
      (hreg : IsRegular M rs) (hrsI : Ideal.ofList rs ≤ I),
      ∃ rs' : List A, IsRegular M (rs ++ rs') ∧
        Ideal.ofList (rs ++ rs') ≤ I ∧ I.depth M = (rs ++ rs').length)
