/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Differential

/-!
# Differential coordinates for module-valued Hom complexes

This leaf turns the two canonical parts of the Hom-complex differential into the three-term
coordinate formulas used by iterated Hom and tensor total complexes.  The formulas are stated on
homogeneous cochains and pure tensors, so downstream developments can use them without unfolding
products, totalizations, or the closed structure.

@stack 0FNE
@stack 0FNF
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex

namespace CategoryTheory.CochainComplex.InternalHom.Module.Differential

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ)

/-- Advancing the inner source degree preserves the outer target index. -/
theorem outerNextIndex (d n : ℤ) :
    (d + 1) + n = d + (n + 1) := by omega

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating an outer Hom-complex differential gives the target differential followed by the
two signed parts of the inner Hom-complex differential. -/
theorem outerDifferential_apply {n : ℤ}
    (z : Cochain (moduleComplex R K L) M n) (d : ℤ)
    (f : Cochain K L d) :
    ModuleCat.Hom.hom
        ((δ n (n + 1) z).v d (d + (n + 1)) rfl) f =
      ModuleCat.Hom.hom (M.d (d + n) (d + (n + 1)))
          (ModuleCat.Hom.hom (z.v d (d + n) rfl) f) +
        (n + 1).negOnePow •
          ModuleCat.Hom.hom
            (z.v (d + 1) (d + (n + 1)) (outerNextIndex d n))
            (Cochain.postDifferential K L d f) +
        ((n + 1).negOnePow * (d + 1).negOnePow) •
          ModuleCat.Hom.hom
            (z.v (d + 1) (d + (n + 1)) (outerNextIndex d n))
            (Cochain.preDifferential K L d f) := by
  have hd : ((moduleComplex R K L).d d (d + 1)).hom f =
      Cochain.postDifferential K L d f +
        (d + 1).negOnePow • Cochain.preDifferential K L d f := by
    dsimp only [moduleComplex, DifferentialGradedCategory.homComplex]
    rw [CochainComplex.of_d]
    change δ d (d + 1) f = _
    apply Cochain.ext
    intro a b hab
    rw [δ_v d (d + 1) rfl f a b hab (a + d) (a + 1) (by omega) rfl]
    rfl
  rw [δ_v n (n + 1) rfl z d (d + (n + 1)) rfl (d + n) (d + 1)
    (by omega) rfl]
  change (M.d (d + n) (d + (n + 1))).hom ((z.v d (d + n) rfl).hom f) +
      (n + 1).negOnePow •
        (z.v (d + 1) (d + (n + 1)) (outerNextIndex d n)).hom
          (((moduleComplex R K L).d d (d + 1)).hom f) = _
  rw [hd]
  simp only [map_add, map_zsmul_unit, smul_add, smul_smul, add_assoc]

/-- For `p + s = n`, the output degree of the outer differential at inner degree `-s - 1` is
`p`. -/
theorem betaTargetIndex {p s n : ℤ} (h : p + s = n) :
    (-s - 1) + (n + 1) = p := by omega

/-- For `p + s = n`, the next inner degree is the source degree of the `p`-th outer
component. -/
theorem betaInnerIndex {p s n : ℤ} (h : p + s = n) :
    ((-s - 1) + 1) + n = p := by omega

/-- Equation 15.72.6.1 (0FNE): the differential of a component `β^{p,s}` has the three
contributions from `M`, `L`, and `K`, with coefficients `1`, `-(-1)^n`, and `(-1)^(p+1)`. -/
@[stacks 0FNE "three-term differential of an iterated Hom component"]
theorem betaDifferential_apply {n p s : ℤ} (h : p + s = n)
    (z : Cochain (moduleComplex R K L) M n)
    (f : Cochain K L (-s - 1)) :
    ModuleCat.Hom.hom
        ((δ n (n + 1) z).v (-s - 1) p (betaTargetIndex h)) f =
      ModuleCat.Hom.hom (M.d ((-s - 1) + n) p)
          (ModuleCat.Hom.hom (z.v (-s - 1) ((-s - 1) + n) rfl) f) +
        (n + 1).negOnePow •
          ModuleCat.Hom.hom
            (z.v ((-s - 1) + 1) p (betaInnerIndex h))
            (Cochain.postDifferential K L (-s - 1) f) +
        (p + 1).negOnePow •
          ModuleCat.Hom.hom
            (z.v ((-s - 1) + 1) p (betaInnerIndex h))
            (Cochain.preDifferential K L (-s - 1) f) := by
  have hsign : (n + 1).negOnePow * ((-s - 1) + 1).negOnePow =
      (p + 1).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    omega
  obtain rfl : p = (-s - 1) + (n + 1) := (betaTargetIndex h).symm
  simpa only [hsign] using outerDifferential_apply K L M z (-s - 1) f

/-- Increasing the Hom-complex degree by one preserves tensor total degree. -/
theorem tensorPostIndex (t r : ℤ) :
    (t + 1) + r = (t + r) + 1 := by omega

/-- Increasing the tensor-factor degree by one preserves tensor total degree. -/
theorem tensorPreIndex (t r : ℤ) :
    t + (r + 1) = (t + r) + 1 := by omega

set_option backward.isDefEq.respectTransparency false in
/-- Equation 15.72.6.2 (0FNF): on `Cochain.single g (p + q) ⊗ₜ k`, the tensor-total
differential is the sum of the `M`, `L`, and `K` differentials with the standard signs. -/
@[stacks 0FNF "three-term tensor-total differential on a pure homogeneous tensor"]
theorem tensorDifferential_single_tmul
    (p q r : ℤ) (g : L.X (-q) ⟶ M.X p) (k : K.X r) :
    ModuleCat.Hom.hom
        ((moduleComplex R L M ⊗ K).d ((p + q) + r) (((p + q) + r) + 1))
        (ModuleCat.Hom.hom
          (HomologicalComplex.ιTensorObj (moduleComplex R L M) K
            (p + q) r ((p + q) + r) rfl)
          (TensorProduct.tmul R (Cochain.single g (p + q)) k)) =
      ModuleCat.Hom.hom
          (HomologicalComplex.ιTensorObj (moduleComplex R L M) K
            ((p + q) + 1) r (((p + q) + r) + 1)
              (tensorPostIndex (p + q) r))
          (TensorProduct.tmul R
            (Cochain.single (g ≫ M.d p (p + 1)) ((p + q) + 1)) k) +
        ((p + q) + 1).negOnePow •
          ModuleCat.Hom.hom
            (HomologicalComplex.ιTensorObj (moduleComplex R L M) K
              ((p + q) + 1) r (((p + q) + r) + 1)
                (tensorPostIndex (p + q) r))
            (TensorProduct.tmul R
              (Cochain.single (L.d (-q - 1) (-q) ≫ g) ((p + q) + 1)) k) +
        (p + q).negOnePow •
          ModuleCat.Hom.hom
            (HomologicalComplex.ιTensorObj (moduleComplex R L M) K
              (p + q) (r + 1) (((p + q) + r) + 1)
                (tensorPreIndex (p + q) r))
            (TensorProduct.tmul R (Cochain.single g (p + q))
              (ModuleCat.Hom.hom (K.d r (r + 1)) k)) := by
  have hd : ((moduleComplex R L M).d (p + q) ((p + q) + 1)).hom
      (Cochain.single g (p + q)) =
        Cochain.single (g ≫ M.d p (p + 1)) ((p + q) + 1) +
          ((p + q) + 1).negOnePow •
            Cochain.single (L.d (-q - 1) (-q) ≫ g) ((p + q) + 1) := by
    dsimp only [moduleComplex, DifferentialGradedCategory.homComplex]
    rw [CochainComplex.of_d]
    change δ (p + q) ((p + q) + 1) (Cochain.single g (p + q)) = _
    exact Cochain.δ_single g (p + q) ((p + q) + 1) rfl
      (-q - 1) (p + 1) (by omega) rfl
  have hι :
      HomologicalComplex.ιTensorObj (moduleComplex R L M) K
          (p + q) r ((p + q) + r) rfl ≫
        (moduleComplex R L M ⊗ K).d ((p + q) + r) (((p + q) + r) + 1) =
      (((moduleComplex R L M).d (p + q) ((p + q) + 1)) ▷ K.X r) ≫
          HomologicalComplex.ιTensorObj (moduleComplex R L M) K
            ((p + q) + 1) r (((p + q) + r) + 1) (tensorPostIndex (p + q) r) +
        (p + q).negOnePow •
          (((moduleComplex R L M).X (p + q) ◁ K.d r (r + 1)) ≫
            HomologicalComplex.ιTensorObj (moduleComplex R L M) K
              (p + q) (r + 1) (((p + q) + r) + 1) (tensorPreIndex (p + q) r)) := by
    change HomologicalComplex.ιMapBifunctor (moduleComplex R L M) K
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
        (p + q) r ((p + q) + r) rfl ≫
      (HomologicalComplex.mapBifunctor (moduleComplex R L M) K
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).d
        ((p + q) + r) (((p + q) + r) + 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show
        (ComplexShape.up ℤ).Rel (p + q) ((p + q) + 1) from rfl)
        r (((p + q) + r) + 1) (tensorPostIndex (p + q) r),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + q) (show
        (ComplexShape.up ℤ).Rel r (r + 1) from rfl)
        (((p + q) + r) + 1) (tensorPreIndex (p + q) r)]
    change (1 : ℤˣ) • _ + _ = _
    simp only [one_smul]
    rfl
  have h := congrArg (fun e ↦ e.hom
    (TensorProduct.tmul R (Cochain.single g (p + q)) k)) hι
  change ((moduleComplex R L M ⊗ K).d
      ((p + q) + r) (((p + q) + r) + 1)).hom
        ((HomologicalComplex.ιTensorObj (moduleComplex R L M) K
          (p + q) r ((p + q) + r) rfl).hom
          (TensorProduct.tmul R (Cochain.single g (p + q)) k)) =
      (HomologicalComplex.ιTensorObj (moduleComplex R L M) K
        ((p + q) + 1) r (((p + q) + r) + 1) (tensorPostIndex (p + q) r)).hom
          (TensorProduct.tmul R
            (((moduleComplex R L M).d (p + q) ((p + q) + 1)).hom
              (Cochain.single g (p + q))) k) +
        (p + q).negOnePow •
          (HomologicalComplex.ιTensorObj (moduleComplex R L M) K
            (p + q) (r + 1) (((p + q) + r) + 1) (tensorPreIndex (p + q) r)).hom
            (TensorProduct.tmul R (Cochain.single g (p + q))
              ((K.d r (r + 1)).hom k)) at h
  simpa only [hd, TensorProduct.add_tmul, ← TensorProduct.smul_tmul',
    map_add, map_zsmul_unit, add_assoc] using h

end CategoryTheory.CochainComplex.InternalHom.Module.Differential
