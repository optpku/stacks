/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.WContractible

/-!
# W-contractible rings

A commutative ring is w-contractible when every faithfully flat weakly étale
ring map out of it admits a retraction.
-/

@[expose] public section

universe u v

#check (IsWContractibleRing : (A : Type u) → [CommRing A] → Prop)

#check (IsWContractibleRing.instIsSepClosed :
  ∀ {K : Type v} [Field K] [IsSepClosed K], IsWContractibleRing K)

#check (IsWContractibleRing.nonempty_algHom :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsWContractibleRing A] [Module.FaithfullyFlat A B] [Algebra.WeaklyEtale A B],
    Nonempty (B →ₐ[A] A))
