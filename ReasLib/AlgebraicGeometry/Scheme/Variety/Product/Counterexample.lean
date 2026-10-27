/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# A product of varieties over a non-algebraically-closed field

This file gives the concrete splitting of the self-fibre product of
`Spec(ℚ(i))` over `Spec(ℚ)` and records its failure to be a variety.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits CommRingCat
open scoped Polynomial TensorProduct

namespace AlgebraicGeometry

/-- The quadratic polynomial cutting out the affine `ℚ`-scheme `Spec(ℚ(i))`. -/
abbrev ratSqrtNegOnePolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 + 1

/-- A concrete model for `ℚ(i)` as `ℚ[X] / (X ^ 2 + 1)`. -/
abbrev ratSqrtNegOne : Type :=
  AdjoinRoot ratSqrtNegOnePolynomial

/-- The affine scheme `Spec(ℚ(i))`. -/
abbrev ratSqrtNegOneSpec : Scheme :=
  Spec (CommRingCat.of ratSqrtNegOne)

/-- The structure morphism `Spec(ℚ(i)) ⟶ Spec(ℚ)`. -/
abbrev ratSqrtNegOneToSpecRat :
    ratSqrtNegOneSpec ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (ofHom (algebraMap ℚ ratSqrtNegOne))

/-- The affine scheme `Spec(ℚ(i))`, viewed as an object over `Spec(ℚ)`. -/
abbrev ratSqrtNegOneOverRat : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk ratSqrtNegOneToSpecRat

private theorem ratSqrtNegOnePolynomial_irreducible :
    Irreducible ratSqrtNegOnePolynomial := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · change (Polynomial.X ^ 2 + Polynomial.C (1 : ℚ)).natDegree ∈ Finset.Icc 1 3
    rw [Polynomial.natDegree_X_pow_add_C]
    decide
  · intro x hx
    have hx' : x ^ 2 + 1 = 0 := by
      simpa [Polynomial.IsRoot, ratSqrtNegOnePolynomial] using hx
    nlinarith [sq_nonneg x]

/-- The affine `ℚ`-scheme `Spec(ℚ(i))` is a variety over `Spec(ℚ)`. -/
instance ratSqrtNegOneOverRatVariety :
    Variety ratSqrtNegOneOverRat := by
  letI : Fact (Irreducible ratSqrtNegOnePolynomial) :=
    ⟨ratSqrtNegOnePolynomial_irreducible⟩
  haveI : LocallyOfFiniteType ratSqrtNegOneToSpecRat := by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine { toIsIntegral := ?_, toIsSeparated := ?_, toFiniteType := ?_ }
  · change IsIntegral ratSqrtNegOneSpec
    infer_instance
  · change IsSeparated ratSqrtNegOneToSpecRat
    infer_instance
  · change Scheme.Hom.FiniteType ratSqrtNegOneToSpecRat
    infer_instance

/-- The self-fibre product `Spec(ℚ(i)) ×[Spec(ℚ)] Spec(ℚ(i))`. -/
abbrev ratSqrtNegOneSelfFiberProduct : Scheme :=
  pullback ratSqrtNegOneToSpecRat ratSqrtNegOneToSpecRat

/-- The self-fibre product of `Spec(ℚ(i))` over `Spec(ℚ)`, viewed over `Spec(ℚ)` through the
first projection. -/
abbrev ratSqrtNegOneSelfFiberProductOverRat :
    Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk
    (pullback.fst ratSqrtNegOneToSpecRat ratSqrtNegOneToSpecRat ≫ ratSqrtNegOneToSpecRat)

/-- The affine tensor-product model `Spec (ℚ(i) ⊗[ℚ] ℚ(i))` of the self-fibre product. -/
abbrev ratSqrtNegOneTensorSelfSpec : Scheme :=
  Spec (CommRingCat.of <| ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne)

/-- The polynomial `X ^ 2 + 1` vanishes at the negative of its adjoined root. -/
theorem ratSqrtNegOnePolynomial_aeval_negRoot :
    Polynomial.eval₂ (algebraMap ℚ ratSqrtNegOne)
      (-AdjoinRoot.root ratSqrtNegOnePolynomial) ratSqrtNegOnePolynomial = 0 := by
  simpa [ratSqrtNegOnePolynomial, AdjoinRoot.algebraMap_eq] using
    AdjoinRoot.eval₂_root ratSqrtNegOnePolynomial

private theorem ratSqrtNegOne_root_sq :
    AdjoinRoot.root ratSqrtNegOnePolynomial ^ 2 = (-1 : ratSqrtNegOne) := by
  apply add_eq_zero_iff_eq_neg.mp
  simpa [ratSqrtNegOnePolynomial, AdjoinRoot.algebraMap_eq] using
    AdjoinRoot.eval₂_root ratSqrtNegOnePolynomial

private theorem ratSqrtNegOne_eq_smul_one_add_smul_root (x : ratSqrtNegOne) :
    ∃ q r : ℚ, x = q • (1 : ratSqrtNegOne) +
      r • AdjoinRoot.root ratSqrtNegOnePolynomial := by
  have hm : ratSqrtNegOnePolynomial.Monic := by
    simpa only [ratSqrtNegOnePolynomial, ← Polynomial.C_1] using
      (Polynomial.monic_X_pow_add_C (R := ℚ) (a := 1) (by decide : 2 ≠ 0))
  have hd : ratSqrtNegOnePolynomial.natDegree = 2 := by
    change (Polynomial.X ^ 2 + Polynomial.C (1 : ℚ)).natDegree = 2
    exact Polynomial.natDegree_X_pow_add_C
  let b : Module.Basis (Fin 2) ℚ ratSqrtNegOne :=
    (AdjoinRoot.powerBasis' hm).basis.reindex (finCongr hd)
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  simpa [Fin.sum_univ_two, b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow] using
    (b.sum_repr x).symm

/-- The conjugation automorphism of `ℚ(i)` sending the adjoined root to its negative. -/
noncomputable def ratSqrtNegOneConj : ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne :=
  AdjoinRoot.liftAlgHom ratSqrtNegOnePolynomial (Algebra.ofId ℚ ratSqrtNegOne)
    (-AdjoinRoot.root ratSqrtNegOnePolynomial) ratSqrtNegOnePolynomial_aeval_negRoot

/-- The diagonal `ℚ`-algebra map `ℚ(i) ⟶ ℚ(i) × ℚ(i)`. -/
noncomputable def ratSqrtNegOneToProdDiagonal :
    ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne × ratSqrtNegOne :=
  (AlgHom.id ℚ ratSqrtNegOne).prod (AlgHom.id ℚ ratSqrtNegOne)

/-- The pair of embeddings `ℚ(i) ⟶ ℚ(i) × ℚ(i)` given by identity and conjugation. -/
noncomputable def ratSqrtNegOneToProdPair :
    ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne × ratSqrtNegOne :=
  (AlgHom.id ℚ ratSqrtNegOne).prod ratSqrtNegOneConj

/-- The `ℚ`-algebra map `ℚ(i) ⊗[ℚ] ℚ(i) ⟶ ℚ(i) × ℚ(i)` induced by identity and
conjugation. -/
noncomputable def ratSqrtNegOneTensorSelfToProd :
    ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne × ratSqrtNegOne :=
  Algebra.TensorProduct.productMap ratSqrtNegOneToProdDiagonal ratSqrtNegOneToProdPair

/-- The explicit inverse map from `ℚ(i) × ℚ(i)` to `ℚ(i) ⊗[ℚ] ℚ(i)`. -/
noncomputable def ratSqrtNegOneProdToTensorSelf :
    ratSqrtNegOne × ratSqrtNegOne → ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne :=
  fun z ↦
    (((1 / 2 : ℚ) • (z.1 + z.2)) ⊗ₜ[ℚ] (1 : ratSqrtNegOne)) +
      (((-(1 / 2 : ℚ)) •
          ((z.1 - z.2) * AdjoinRoot.root ratSqrtNegOnePolynomial)) ⊗ₜ[ℚ]
        AdjoinRoot.root ratSqrtNegOnePolynomial)

private theorem ratSqrtNegOneProdToTensorSelf_add
    (x y : ratSqrtNegOne × ratSqrtNegOne) :
    ratSqrtNegOneProdToTensorSelf (x + y) =
      ratSqrtNegOneProdToTensorSelf x + ratSqrtNegOneProdToTensorSelf y := by
  simp only [ratSqrtNegOneProdToTensorSelf, Prod.fst_add, Prod.snd_add]
  rw [show x.1 + y.1 + (x.2 + y.2) = (x.1 + x.2) + (y.1 + y.2) by abel,
    show x.1 + y.1 - (x.2 + y.2) = (x.1 - x.2) + (y.1 - y.2) by abel]
  simp only [add_mul, smul_add, TensorProduct.add_tmul]
  abel

private theorem ratSqrtNegOneProdToTensorSelf_smul
    (q : ℚ) (x : ratSqrtNegOne × ratSqrtNegOne) :
    ratSqrtNegOneProdToTensorSelf (q • x) =
      q • ratSqrtNegOneProdToTensorSelf x := by
  simp only [ratSqrtNegOneProdToTensorSelf, Prod.smul_fst, Prod.smul_snd,
    ← smul_add, ← smul_sub, smul_mul_assoc, smul_smul]
  simp only [smul_add, TensorProduct.smul_tmul', smul_smul, mul_comm]

/-- The tensor product `ℚ(i) ⊗[ℚ] ℚ(i)` splits as `ℚ(i) × ℚ(i)`. -/
noncomputable def ratSqrtNegOneTensorSelfEquivProd :
    ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne ≃+* (ratSqrtNegOne × ratSqrtNegOne) where
  toFun := ratSqrtNegOneTensorSelfToProd
  invFun := ratSqrtNegOneProdToTensorSelf
  left_inv := by
    have h_one (a : ratSqrtNegOne) :
        ratSqrtNegOneProdToTensorSelf
          (ratSqrtNegOneTensorSelfToProd (a ⊗ₜ[ℚ] (1 : ratSqrtNegOne))) =
            a ⊗ₜ[ℚ] (1 : ratSqrtNegOne) := by
      have h : (1 / 2 : ℚ) • (a + a) = a := by module
      simpa [ratSqrtNegOneProdToTensorSelf, ratSqrtNegOneTensorSelfToProd,
        Algebra.TensorProduct.productMap_apply_tmul, ratSqrtNegOneToProdDiagonal,
        ratSqrtNegOneToProdPair] using congrArg
          (fun z : ratSqrtNegOne => z ⊗ₜ[ℚ] (1 : ratSqrtNegOne)) h
    have h_root (a : ratSqrtNegOne) :
        ratSqrtNegOneProdToTensorSelf
          (ratSqrtNegOneTensorSelfToProd
            (a ⊗ₜ[ℚ] AdjoinRoot.root ratSqrtNegOnePolynomial)) =
              a ⊗ₜ[ℚ] AdjoinRoot.root ratSqrtNegOnePolynomial := by
      have h : (-(1 / 2 : ℚ)) •
          ((a * AdjoinRoot.root ratSqrtNegOnePolynomial -
              -(a * AdjoinRoot.root ratSqrtNegOnePolynomial)) *
            AdjoinRoot.root ratSqrtNegOnePolynomial) = a := by
        simp only [sub_neg_eq_add, add_mul, mul_assoc, ← sq, ratSqrtNegOne_root_sq,
          mul_neg, mul_one]
        module
      simpa [ratSqrtNegOneProdToTensorSelf, ratSqrtNegOneTensorSelfToProd,
        Algebra.TensorProduct.productMap_apply_tmul, ratSqrtNegOneToProdDiagonal,
        ratSqrtNegOneToProdPair, ratSqrtNegOneConj] using congrArg
          (fun z : ratSqrtNegOne => z ⊗ₜ[ℚ] AdjoinRoot.root ratSqrtNegOnePolynomial) h
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [ratSqrtNegOneProdToTensorSelf]
    | tmul a b =>
      obtain ⟨q, r, rfl⟩ := ratSqrtNegOne_eq_smul_one_add_smul_root b
      simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, map_add, map_smul,
        ratSqrtNegOneProdToTensorSelf_add, ratSqrtNegOneProdToTensorSelf_smul, h_one, h_root]
    | add x y hx hy =>
      rw [map_add, ratSqrtNegOneProdToTensorSelf_add, hx, hy]
  right_inv := by
    intro z
    ext <;>
      simp [ratSqrtNegOneProdToTensorSelf, ratSqrtNegOneTensorSelfToProd,
        Algebra.TensorProduct.productMap_apply_tmul, ratSqrtNegOneToProdDiagonal,
        ratSqrtNegOneToProdPair, ratSqrtNegOneConj,
        mul_assoc, ← sq, ratSqrtNegOne_root_sq] <;>
      module
  map_mul' := ratSqrtNegOneTensorSelfToProd.map_mul
  map_add' := ratSqrtNegOneTensorSelfToProd.map_add

/-- The spectrum of `ℚ(i) ⊗[ℚ] ℚ(i)` is isomorphic to the spectrum of
`ℚ(i) × ℚ(i)`. -/
noncomputable def ratSqrtNegOneTensorSelfSpecIsoSpecProd :
    ratSqrtNegOneTensorSelfSpec ≅ Spec (CommRingCat.of (ratSqrtNegOne × ratSqrtNegOne)) where
  hom := Spec.map (ofHom ratSqrtNegOneTensorSelfEquivProd.symm.toRingHom)
  inv := Spec.map (ofHom ratSqrtNegOneTensorSelfEquivProd.toRingHom)
  hom_inv_id :=
    (Scheme.Spec.mapIso
      ratSqrtNegOneTensorSelfEquivProd.symm.toCommRingCatIso.op).hom_inv_id
  inv_hom_id :=
    (Scheme.Spec.mapIso
      ratSqrtNegOneTensorSelfEquivProd.symm.toCommRingCatIso.op).inv_hom_id

/-- The self-fibre product of `Spec(ℚ(i))` over `Spec(ℚ)` is isomorphic to the coproduct of
two copies of `Spec(ℚ(i))`. -/
noncomputable def ratSqrtNegOneSelfFiberProductIsoCoprod :
    ratSqrtNegOneSelfFiberProduct ≅ ratSqrtNegOneSpec ⨿ ratSqrtNegOneSpec :=
  pullbackSpecIso ℚ ratSqrtNegOne ratSqrtNegOne ≪≫
    ratSqrtNegOneTensorSelfSpecIsoSpecProd ≪≫
      (asIso (coprodSpec ratSqrtNegOne ratSqrtNegOne)).symm

/-- The self-fibre product of `Spec(ℚ(i))` over `Spec(ℚ)` is reducible. -/
theorem ratSqrtNegOneSelfFiberProductReducible :
    ¬ IrreducibleSpace ratSqrtNegOneSelfFiberProduct := by
  intro h
  haveI : IsIntegral ratSqrtNegOneSpec := ratSqrtNegOneOverRatVariety.toIsIntegral
  let e := (coprodMk ratSqrtNegOneSpec ratSqrtNegOneSpec).trans
    ratSqrtNegOneSelfFiberProductIsoCoprod.inv.homeomorph
  haveI : IrreducibleSpace (ratSqrtNegOneSpec ⊕ ratSqrtNegOneSpec) :=
    e.irreducibleSpace_iff.mpr h
  obtain ⟨x, ⟨a, ha⟩, ⟨b, hb⟩⟩ := nonempty_preirreducible_inter
    (isOpen_range_inl (X := ratSqrtNegOneSpec) (Y := ratSqrtNegOneSpec))
    isOpen_range_inr (Set.range_nonempty _) (Set.range_nonempty _)
  cases ha.trans hb.symm

/-- The self-fibre product of the `ℚ`-variety `Spec(ℚ(i))` with itself over `Spec(ℚ)` is not
a variety. -/
theorem ratSqrtNegOneSelfFiberProductOverRatNotVariety :
    ¬ Variety ratSqrtNegOneSelfFiberProductOverRat := by
  intro h
  haveI : IsIntegral ratSqrtNegOneSelfFiberProduct := h.toIsIntegral
  exact ratSqrtNegOneSelfFiberProductReducible inferInstance

end AlgebraicGeometry
