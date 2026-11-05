/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.WeaklyEtale

/-!
# W-contractible rings

A commutative ring is w-contractible when every faithfully flat weakly étale
ring map out of it admits a retraction.
-/

@[expose] public section

universe u v

/-- A commutative ring is w-contractible when every faithfully flat weakly étale
ring map out of it into a ring in the test universe `v` admits a retraction.
Use `IsWContractibleRing.{u, u} A` for the usual same-universe property. -/
@[mk_iff, stacks 0981]
class IsWContractibleRing (A : Type u) [CommRing A] : Prop where
  /-- Every faithfully flat weakly étale ring map out of `A` has a retraction. -/
  exists_retraction {B : Type v} [CommRing B] (f : A →+* B)
      (hf : f.FaithfullyFlat) (hwe : f.WeaklyEtale) :
    ∃ r : B →+* A, r.comp f = RingHom.id A

namespace IsWContractibleRing

/-- A separably closed field is w-contractible. -/
instance instIsSepClosed {K : Type v} [Field K] [IsSepClosed K] :
    IsWContractibleRing K := sorry

/-- A faithfully flat weakly étale algebra over a ring that is w-contractible
for the universe of that algebra admits an `A`-algebra retraction. -/
theorem nonempty_algHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsWContractibleRing.{u, v} A] [Module.FaithfullyFlat A B]
    [Algebra.WeaklyEtale A B] : Nonempty (B →ₐ[A] A) := by
  obtain ⟨r, hr⟩ := exists_retraction (algebraMap A B)
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    (by
      change @Algebra.WeaklyEtale A B _ _ (algebraMap A B).toAlgebra
      rw [toAlgebra_algebraMap]
      infer_instance)
  exact ⟨{ r with commutes' := fun a => congrArg (fun f : A →+* A => f a) hr }⟩

end IsWContractibleRing
