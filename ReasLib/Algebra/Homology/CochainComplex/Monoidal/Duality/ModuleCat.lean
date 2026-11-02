/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Duality.Module

/-!
# Exact pairings of module cochain complexes

An exact pairing of module cochain complexes restricts on total degree zero to exact pairings of
opposite homogeneous degrees.  This file owns the concrete diagonal projection and the resulting
degreewise pairing, together with boundedness, finite-projectivity, and linear-dual consequences.
The pairing is passed explicitly, so consumers do not need temporary instances.

@stack 0FNK
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open ComplexShape HomologicalComplex
open scoped TensorProduct

namespace CategoryTheory.CochainComplex.Duality

variable {R : Type u} [CommRing R]
variable {M N : CochainComplex (ModuleCat R) ℤ}

/-- The tensor summand in bidegree `(i,j)`. -/
@[stacks 0FNK "tensor summand in a totalized module complex"]
abbrev tensorSummand
    (M N : CochainComplex (ModuleCat R) ℤ) (i j : ℤ) : ModuleCat R :=
  ((curriedTensor (ModuleCat R)).obj (M.X i)).obj (N.X j)

/-- Projection from total tensor degree zero to the summand in bidegree `(n,-n)`. -/
@[stacks 0FNK "diagonal projection from a tensor totalization"]
noncomputable def diagonalProjection
    (M N : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ((M ⊗ N).X 0) ⟶ tensorSummand M N n (-n) :=
  HomologicalComplex.mapBifunctorDesc fun i j _ ↦
    if hi : i = n then
      if hj : j = -n then
        eqToHom (congrArg₂ (tensorSummand M N) hi hj)
      else 0
    else 0

/-- The degree-`(n,-n)` coevaluation extracted from an exact pairing of cochain complexes. -/
@[stacks 0FNK "degreewise coevaluation of an exact pairing"]
noncomputable def degreewiseCoevaluation
    (p : ExactPairing M N) (n : ℤ) :
    𝟙_ (ModuleCat R) ⟶ (M.X n ⊗ N.X (-n) : ModuleCat R) :=
  (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
    p.coevaluation'.f 0 ≫ diagonalProjection M N n

/-- The degree-`(-n,n)` evaluation extracted from an exact pairing of cochain complexes. -/
@[stacks 0FNK "degreewise evaluation of an exact pairing"]
noncomputable def degreewiseEvaluation
    (p : ExactPairing M N) (n : ℤ) :
    (N.X (-n) ⊗ M.X n : ModuleCat R) ⟶ 𝟙_ (ModuleCat R) :=
  ιTensorObj N M (-n) n 0 (neg_add_cancel n) ≫
    p.evaluation'.f 0 ≫
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom

/-- Restricting a complex exact pairing to bidegree `(n,-n)` gives an exact pairing of the
corresponding terms. -/
@[stacks 0FNK "degreewise exact pairing", implicit_reducible]
noncomputable def degreewise (p : ExactPairing M N) (n : ℤ) :
    ExactPairing (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R) where
  coevaluation' := degreewiseCoevaluation p n
  evaluation' := degreewiseEvaluation p n
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- The coevaluation at degree `-n`, reindexed so that its second term is literally `N^n`. -/
@[stacks 0FNK "reindexed degreewise coevaluation"]
noncomputable def degreewiseNegCoevaluation (p : ExactPairing M N) (n : ℤ) :
    𝟙_ (ModuleCat R) ⟶ (M.X (-n) ⊗ N.X n : ModuleCat R) :=
  degreewiseCoevaluation p (-n) ≫
    (𝟙 (M.X (-n) : ModuleCat R) ⊗ₘ eqToHom (congrArg N.X (neg_neg n)))

/-- The evaluation at degree `-n`, reindexed so that its first term is literally `N^n`. -/
@[stacks 0FNK "reindexed degreewise evaluation"]
noncomputable def degreewiseNegEvaluation (p : ExactPairing M N) (n : ℤ) :
    (N.X n ⊗ M.X (-n) : ModuleCat R) ⟶ 𝟙_ (ModuleCat R) :=
  (eqToHom (congrArg N.X (neg_neg n)).symm ⊗ₘ 𝟙 (M.X (-n) : ModuleCat R)) ≫
    degreewiseEvaluation p (-n)

/-- The degreewise pairing at `-n`, with its second term transported from degree `-(-n)` to
degree `n`. -/
@[stacks 0FNK "reindexed degreewise exact pairing", implicit_reducible]
noncomputable def degreewiseNeg (p : ExactPairing M N) (n : ℤ) :
    ExactPairing (M.X (-n) : ModuleCat R) (N.X n : ModuleCat R) where
  coevaluation' := degreewiseNegCoevaluation p n
  evaluation' := degreewiseNegEvaluation p n
  coevaluation_evaluation' := by
    letI := degreewise p (-n)
    let q : ExactPairing (M.X (-n) : ModuleCat R) (N.X n : ModuleCat R) :=
      exactPairingCongrRight (eqToIso (congrArg N.X (neg_neg n))).symm
    have h := @ExactPairing.coevaluation_evaluation' (ModuleCat R) _ _ _ _ q
    change (N.X n : ModuleCat R) ◁ degreewiseNegCoevaluation p n ≫
        (α_ (N.X n) (M.X (-n)) (N.X n)).inv ≫
          degreewiseNegEvaluation p n ▷ (N.X n : ModuleCat R) =
        (ρ_ (N.X n : ModuleCat R)).hom ≫ (λ_ (N.X n : ModuleCat R)).inv at h
    exact h
  evaluation_coevaluation' := by
    letI := degreewise p (-n)
    let q : ExactPairing (M.X (-n) : ModuleCat R) (N.X n : ModuleCat R) :=
      exactPairingCongrRight (eqToIso (congrArg N.X (neg_neg n))).symm
    have h := @ExactPairing.evaluation_coevaluation' (ModuleCat R) _ _ _ _ q
    change degreewiseNegCoevaluation p n ▷ (M.X (-n) : ModuleCat R) ≫
        (α_ (M.X (-n)) (N.X n) (M.X (-n))).hom ≫
          (M.X (-n) : ModuleCat R) ◁ degreewiseNegEvaluation p n =
        (λ_ (M.X (-n) : ModuleCat R)).hom ≫ (ρ_ (M.X (-n) : ModuleCat R)).inv at h
    exact h

/-- The first complex in an exact pairing of module complexes is bounded. -/
@[stacks 0FNK "boundedness of a dualizable module complex"]
theorem left_bounded (p : ExactPairing M N) :
    CochainComplex.bounded (ModuleCat R) M := sorry

/-- The second complex in an exact pairing of module complexes is bounded. -/
@[stacks 0FNK "boundedness of a dualizable module complex"]
theorem right_bounded (p : ExactPairing M N) :
    CochainComplex.bounded (ModuleCat R) N := by
  have hz (n : ℤ) (hm : IsZero (M.X (-n))) : IsZero (N.X n) := by
    letI : Subsingleton (M.X (-n)) := ModuleCat.isZero_iff_subsingleton.mp hm
    have hdual : IsZero (ModuleCat.of R (Module.Dual R (M.X (-n)))) :=
      ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    exact hdual.of_iso (degreewiseNeg p n).moduleDualIso.symm
  rcases left_bounded p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [_root_.CochainComplex.isStrictlyGE_iff] at ha
  rw [_root_.CochainComplex.isStrictlyLE_iff] at hb
  refine ⟨⟨-b, ?_⟩, ⟨-a, ?_⟩⟩
  · rw [_root_.CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact hz n (hb (-n) (by omega))
  · rw [_root_.CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact hz n (ha (-n) (by omega))

/-- Every term of the first complex in an exact pairing is finite projective. -/
@[stacks 0FNK "finite-projective terms of a dualizable module complex"]
theorem left_finiteProjective (p : ExactPairing M N) (n : ℤ) :
    Module.FiniteProjective R (M.X n) :=
  (degreewise p n).left_finiteProjective

/-- Every term of the second complex in an exact pairing is finite projective. -/
@[stacks 0FNK "finite-projective terms of a dualizable module complex"]
theorem right_finiteProjective (p : ExactPairing M N) (n : ℤ) :
    Module.FiniteProjective R (N.X n) :=
  (degreewiseNeg p n).right_finiteProjective

/-- Evaluation in degree `n` identifies `N^n` with a functional on `M^{-n}`. -/
@[stacks 0FNK "degreewise map to the linear dual"]
noncomputable def rightTermHom (p : ExactPairing M N) (n : ℤ) :
    N.X n ⟶ ModuleCat.of R (Module.Dual R (M.X (-n))) :=
  ExactPairing.toModuleDualOfEvaluation (degreewiseNegEvaluation p n)

/-- On a pure tensor, the degreewise dual comparison recovers the original evaluation. -/
theorem rightTermHom_apply (p : ExactPairing M N) (n : ℤ)
    (x : N.X n) (y : M.X (-n)) :
    rightTermHom p n x y =
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom
        (p.evaluation'.f 0
          (ιTensorObj N M n (-n) 0 (add_neg_cancel n) (x ⊗ₜ[R] y))) := by
  change (((MonoidalClosed.curry
    ((β_ (M.X (-n) : ModuleCat R) (N.X n : ModuleCat R)).hom ≫
      degreewiseNegEvaluation p n)).hom x).hom y) = _
  rw [ModuleCat.monoidalClosed_curry]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.braiding_hom_apply]
  have he {i j : ℤ} (hij : i = j) (hi : i + -n = 0) :
      (eqToHom (congrArg N.X hij).symm ⊗ₘ 𝟙 (M.X (-n) : ModuleCat R)) ≫
        ιTensorObj N M i (-n) 0 hi =
      ιTensorObj N M j (-n) 0 (by omega) := by
    subst j
    simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp]
  change ((eqToHom (congrArg N.X (neg_neg n)).symm ⊗ₘ
      𝟙 (M.X (-n) : ModuleCat R)) ≫
        (ιTensorObj N M (-(-n)) (-n) 0 (neg_add_cancel (-n)) ≫
          p.evaluation'.f 0 ≫
            (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom)) (x ⊗ₜ[R] y) = _
  rw [← Category.assoc, he (neg_neg n)]
  rfl

/-- Coevaluation in degree `-n` sends a functional on `M^{-n}` back to `N^n`. -/
@[stacks 0FNK "degreewise map from the linear dual"]
def rightTermInv (p : ExactPairing M N) (n : ℤ) :
    ModuleCat.of R (Module.Dual R (M.X (-n))) ⟶ N.X n :=
  ExactPairing.fromCoevaluation (degreewiseNegCoevaluation p n)

/-- The term `N^n` is canonically the linear dual of `M^{-n}`.  Both maps are explicit in the
degreewise evaluation and coevaluation; only their inverse laws use the triangle identities. -/
@[stacks 0FNK "degreewise linear-dual identification"]
noncomputable def rightTermIso (p : ExactPairing M N) (n : ℤ) :
    N.X n ≅ ModuleCat.of R (Module.Dual R (M.X (-n))) where
  hom := rightTermHom p n
  inv := rightTermInv p n
  hom_inv_id := by
    have h := (degreewiseNeg p n).moduleDualIso.inv_hom_id
    change rightTermHom p n ≫ rightTermInv p n = 𝟙 (N.X n : ModuleCat R) at h
    exact h
  inv_hom_id := by
    have h := (degreewiseNeg p n).moduleDualIso.hom_inv_id
    change rightTermInv p n ≫ rightTermHom p n =
      𝟙 (ModuleCat.of R (Module.Dual R (M.X (-n)))) at h
    exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the degreewise dual identifications, the differential on the second complex is the
signed transpose of the differential on the first complex. -/
@[stacks 0FNK "signed transpose differential on a dual complex"]
theorem rightTermIso_d_comm (p : ExactPairing M N) (n : ℤ) :
    CommSq (N.d n (n + 1))
      (rightTermIso p n).hom
      (rightTermIso p (n + 1)).hom
      ((-n.negOnePow) •
        ModuleCat.ofHom
          ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) :
            Module.Dual R (M.X (-n)) →ₗ[R] Module.Dual R (M.X (-(n + 1))))) := by
  have hu : (𝟙_ (CochainComplex (ModuleCat R) ℤ)).d (-1) 0 = 0 := by
    change ((single (ModuleCat R) (up ℤ) 0).obj (𝟙_ (ModuleCat R))).d (-1) 0 = 0
    exact single_obj_d (up ℤ) 0 (𝟙_ (ModuleCat R)) (-1) 0
  have hc : ιTensorObj N M n (-(n + 1)) (-1) (by omega) ≫
      (N ⊗ M).d (-1) 0 ≫ p.evaluation'.f 0 ≫
        (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom = 0 := by
    rw [← p.evaluation'.comm_assoc, hu, zero_comp, comp_zero, comp_zero]
  change ιMapBifunctor N M (curriedTensor (ModuleCat R)) (up ℤ)
      n (-(n + 1)) (-1) (by dsimp; omega) ≫
      (mapBifunctor N M (curriedTensor (ModuleCat R)) (up ℤ)).d (-1) 0 ≫
        p.evaluation'.f 0 ≫
          (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom = 0 at hc
  rw [mapBifunctor.d_eq] at hc
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc] at hc
  rw [mapBifunctor.d₁_eq N M (curriedTensor (ModuleCat R)) (up ℤ)
      (show (up ℤ).Rel n (n + 1) from rfl) (-(n + 1)) 0 (by dsimp; omega),
    mapBifunctor.d₂_eq N M (curriedTensor (ModuleCat R)) (up ℤ) n
      (show (up ℤ).Rel (-(n + 1)) (-n) by change -(n + 1) + 1 = -n; omega)
      0 (by dsimp; omega)] at hc
  have hε₁ : ε₁ (up ℤ) (up ℤ) (up ℤ) (n, -(n + 1)) = 1 := rfl
  have hε₂ : ε₂ (up ℤ) (up ℤ) (up ℤ) (n, -(n + 1)) = n.negOnePow := rfl
  rw [hε₁, hε₂, one_smul, Linear.units_smul_comp] at hc
  change ((N.d n (n + 1) ▷ (M.X (-(n + 1)) : ModuleCat R)) ≫
      ιTensorObj N M (n + 1) (-(n + 1)) 0 (add_neg_cancel (n + 1)) ≫
        p.evaluation'.f 0 ≫ (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom) +
    n.negOnePow • (((N.X n : ModuleCat R) ◁ M.d (-(n + 1)) (-n)) ≫
      ιTensorObj N M n (-n) 0 (add_neg_cancel n) ≫
        p.evaluation'.f 0 ≫ (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom) = 0 at hc
  constructor
  ext x y
  change rightTermHom p (n + 1) ((N.d n (n + 1)) x) y =
    (-n.negOnePow) • rightTermHom p n x ((M.d (-(n + 1)) (-n)) y)
  rw [rightTermHom_apply, rightTermHom_apply]
  have hxy := congrArg (fun f ↦ ModuleCat.Hom.hom f (x ⊗ₜ[R] y)) hc
  simp only [ModuleCat.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at hxy
  change _ + n.negOnePow • _ = (0 : R) at hxy
  have hneg := eq_neg_of_add_eq_zero_left hxy
  simp only [Units.smul_def, Units.val_neg, neg_smul] at hneg ⊢
  convert! hneg using 1 <;> rfl

end CategoryTheory.CochainComplex.Duality
