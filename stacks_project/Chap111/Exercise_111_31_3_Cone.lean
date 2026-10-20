/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Cone

/-!
# Cones in classical affine space

A subset of the `k`-points of affine space is a cone when it is closed under
scalar multiplication.
-/

universe u v

#check (MvPolynomial.IsCone :
  {k : Type u} → {σ : Type v} → [Field k] → Set (σ → k) → Prop)

#check (MvPolynomial.isCone_iff :
  ∀ {k : Type u} {σ : Type v} [Field k] (X : Set (σ → k)),
    MvPolynomial.IsCone X ↔ ∀ x ∈ X, ∀ c : k, (fun i ↦ c * x i) ∈ X)

#check (MvPolynomial.isCone_zeroLocus_span :
  ∀ {k : Type u} {σ : Type v} [Field k] (S : Set (MvPolynomial σ k)),
    (∀ f ∈ S, ∃ d, f.IsHomogeneous d) →
      MvPolynomial.IsCone (MvPolynomial.zeroLocus k (Ideal.span S)))
