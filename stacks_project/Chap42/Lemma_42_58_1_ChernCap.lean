/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter
public import stacks_project.Chap42.Lemma_42_54_5
public import stacks_project.Chap42.Proposition_42_57_1_ChernCap

/-!
# Chern character capped on the fundamental class

This file packages the composition `K₀(Vect(X)) ⊗ ℚ → A^*(X) ⊗ ℚ → CH_*(X) ⊗ ℚ` of
the Chern character on vector-bundle K-theory with identity-square cap against `[X]`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChowGroup
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped BigOperators DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable (X : Over S) [LocallyOfFiniteType X.hom]

/-- The supremum of `|δ_{X/S}|`. -/
noncomputable def relativeDimensionAbsBound
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) : ℕ :=
  (fun _ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs) ↦
    sSup (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) hδ

/-- `relativeDimensionAbsBound` is the supremum of the absolute values of `δ_{X/S}`. -/
theorem relativeDimensionAbsBound_def
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) :
    relativeDimensionAbsBound δ X hδ =
      sSup (Set.range fun x : X.left ↦
        (X.hom.relativeDimensionFunction δ x).natAbs) :=
  sorry

/-- Chern-degree cutoff covering every codimension that can meet a cycle of degree
in `[-B, B]`, where `B` is `relativeDimensionAbsBound`. -/
noncomputable def chernDegreeBound
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) : ℕ :=
  2 * relativeDimensionAbsBound δ X hδ

/-- `chernDegreeBound` is twice `relativeDimensionAbsBound`. -/
theorem chernDegreeBound_def
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) :
    chernDegreeBound δ X hδ = 2 * relativeDimensionAbsBound δ X hδ :=
  sorry

/-- Identity-square cap of a homogeneous operational class against `[X]_n`. -/
noncomputable def identitySquareCap (p n : ℤ) :
    ChowCohomology.degree δ X.hom p →+ RelativeChow δ X (n - p) where
  toFun c :=
    c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
      IsPullback.of_id_snd n (fundamentalClass_mk δ X.hom n)
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of `identitySquareCap` is the identity-square cap of `[X]_n`. -/
theorem identitySquareCap_apply (p n : ℤ) (c : ChowCohomology.degree δ X.hom p) :
    identitySquareCap δ X p n c =
      c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd n (fundamentalClass_mk δ X.hom n) :=
  sorry

/-- The `ℚ`-linear extension of `chernCharacter` on `K₀(Vect(X)) ⊗ ℚ`. -/
noncomputable def chernCharacter_tensorQ (classes : ChernClass.Theory δ X.hom) :
    TensorProduct ℤ (VectorBundleK0 X.left) ℚ →+
      ChowCohomology.Nonnegative.RationalCompletion δ X.hom :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun q =>
            fun i =>
              TensorProduct.map
                (LinearMap.id :
                  ChowCohomology.Nonnegative.degree δ X.hom i →ₗ[ℤ]
                    ChowCohomology.Nonnegative.degree δ X.hom i)
                (AddMonoidHom.mulLeft q).toIntLinearMap
                (chernCharacter δ X.hom classes a i)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- On a pure tensor, `chernCharacter_tensorQ` scales the Chern character on each degree. -/
theorem chernCharacter_tensorQ_tmul (classes : ChernClass.Theory δ X.hom)
    (a : VectorBundleK0 X.left) (q : ℚ) :
    chernCharacter_tensorQ δ X classes (a ⊗ₜ[ℤ] q) =
      fun i =>
        TensorProduct.map
          (LinearMap.id :
            ChowCohomology.Nonnegative.degree δ X.hom i →ₗ[ℤ]
              ChowCohomology.Nonnegative.degree δ X.hom i)
          (AddMonoidHom.mulLeft q).toIntLinearMap
          (chernCharacter δ X.hom classes a i) :=
  sorry

/-- The integral composite of `chernCharacter` with identity-square cap against `[X]`. -/
noncomputable def toRationalChowAdd [CompactSpace X.left]
    (classes : ChernClass.Theory δ X.hom)
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) :
    VectorBundleK0 X.left →+ rationalChow δ X where
  toFun a :=
    ∑ i ∈ Finset.range (chernDegreeBound δ X hδ + 1),
      ∑ n ∈ relativeDimensionDegrees δ X,
        TensorProduct.map
          (DirectSum.lof ℤ ℤ (fun d ↦ RelativeChow δ X d) (n - (i : ℤ)))
          (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
          (TensorProduct.map (identitySquareCap δ X (i : ℤ) n).toIntLinearMap
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
            (chernCharacter δ X.hom classes a i))
  map_zero' := sorry
  map_add' := sorry

/-- `toRationalChowAdd` is the double sum of identity-square caps of Chern components
against `[X]_n`. -/
theorem toRationalChowAdd_apply [CompactSpace X.left]
    (classes : ChernClass.Theory δ X.hom)
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs))
    (a : VectorBundleK0 X.left) :
    toRationalChowAdd δ X classes hδ a =
      ∑ i ∈ Finset.range (chernDegreeBound δ X hδ + 1),
        ∑ n ∈ relativeDimensionDegrees δ X,
          TensorProduct.map
            (DirectSum.lof ℤ ℤ (fun d ↦ RelativeChow δ X d) (n - (i : ℤ)))
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
            (TensorProduct.map (identitySquareCap δ X (i : ℤ) n).toIntLinearMap
              (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
              (chernCharacter δ X.hom classes a i)) :=
  sorry

/-- The `ℚ`-linear extension `K₀(Vect(X)) ⊗ ℚ → CH_*(X) ⊗ ℚ` of `toRationalChowAdd`. -/
noncomputable def toRationalChow_tensorQ [CompactSpace X.left]
    (classes : ChernClass.Theory δ X.hom)
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) :
    TensorProduct ℤ (VectorBundleK0 X.left) ℚ →+ rationalChow δ X :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun q => smulRationalChow δ X q (toRationalChowAdd δ X classes hδ a)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- On a pure tensor, `toRationalChow_tensorQ` scales `toRationalChowAdd`. -/
theorem toRationalChow_tensorQ_tmul [CompactSpace X.left]
    (classes : ChernClass.Theory δ X.hom)
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs))
    (a : VectorBundleK0 X.left) (q : ℚ) :
    toRationalChow_tensorQ δ X classes hδ (a ⊗ₜ[ℤ] q) =
      smulRationalChow δ X q (toRationalChowAdd δ X classes hδ a) :=
  sorry

/-- The composite on `K₀(Vect(X)) ⊗ ℚ` is identity-square cap of `chernCharacter_tensorQ`
against the degree pieces of `[X]`. -/
theorem toRationalChow_comp [CompactSpace X.left]
    (classes : ChernClass.Theory δ X.hom)
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs))
    (z : TensorProduct ℤ (VectorBundleK0 X.left) ℚ) :
    toRationalChow_tensorQ δ X classes hδ z =
      ∑ i ∈ Finset.range (chernDegreeBound δ X hδ + 1),
        ∑ n ∈ relativeDimensionDegrees δ X,
          TensorProduct.map
            (DirectSum.lof ℤ ℤ (fun d ↦ RelativeChow δ X d) (n - (i : ℤ)))
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
            (TensorProduct.map (identitySquareCap δ X (i : ℤ) n).toIntLinearMap
              (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
              (chernCharacter_tensorQ δ X classes z i)) :=
  sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
