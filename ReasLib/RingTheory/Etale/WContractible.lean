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
ring map out of it admits a retraction. -/
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

/-- A faithfully flat weakly étale algebra over a w-contractible ring admits an
`A`-algebra retraction. -/
theorem nonempty_algHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsWContractibleRing A] [Module.FaithfullyFlat A B]
    [Algebra.WeaklyEtale A B] : Nonempty (B →ₐ[A] A) := sorry

end IsWContractibleRing
