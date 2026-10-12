/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

universe u

noncomputable section

namespace AlgEquiv

/-- The unique extension of a separable-closure automorphism to an algebraic closure is inverse
to restriction along the closure tower. -/
theorem liftNormal_restrictNormal_of_isAlgClosure (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosure K Kbar] [IsSepClosure K Ksep]
    (σ : Gal(Kbar/K)) :
    (σ.restrictNormal Ksep).liftNormal Kbar = σ := sorry

/-- Unique extension of separable-closure automorphisms to an algebraic closure preserves
multiplication. -/
theorem liftNormal_mul_of_isAlgClosure (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosure K Kbar] [IsSepClosure K Ksep]
    (σ τ : Gal(Ksep/K)) :
    (σ * τ).liftNormal Kbar = σ.liftNormal Kbar * τ.liftNormal Kbar := sorry

/-- The automorphism groups of a separable closure and an algebraic closure are equivalent by
unique extension and restriction. -/
noncomputable def sepClosureEquivAlgClosure (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosure K Kbar] [IsSepClosure K Ksep] :
    Gal(Ksep/K) ≃* Gal(Kbar/K) where
  toFun σ := σ.liftNormal Kbar
  invFun σ := AlgEquiv.restrictNormalHom Ksep σ
  left_inv σ := by
    change (σ.liftNormal Kbar).restrictNormal Ksep = σ
    exact AlgEquiv.restrict_liftNormal Kbar σ
  right_inv σ := AlgEquiv.liftNormal_restrictNormal_of_isAlgClosure K Kbar Ksep σ
  map_mul' σ τ := AlgEquiv.liftNormal_mul_of_isAlgClosure K Kbar Ksep σ τ

/-- Restriction is the inverse component of the closure automorphism equivalence. -/
theorem sepClosureEquivAlgClosure_symm_apply (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosure K Kbar] [IsSepClosure K Ksep]
    (σ : Gal(Kbar/K)) :
    (sepClosureEquivAlgClosure K Kbar Ksep).symm σ =
      AlgEquiv.restrictNormalHom Ksep σ := rfl

end AlgEquiv

end
