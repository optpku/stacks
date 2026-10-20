/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.SingletonDifferential
import StacksCheckRecall

@[expose] public section

noncomputable section

/-!
Head/tail exactness support for Remark 10.69.7 (Other types of regular sequences).
@stack 061T
-/

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the finite-family carried by a
cons list is the canonical `Fin.cons` head-plus-tail family. -/
theorem cons_list_get_eq_fin_cons {A : Type u} [CommRing A] (r : A) (rs : List A) :
    (r :: rs).get = Fin.cons r rs.get := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): mapping a cons list through a
ring homomorphism and then passing to the canonical finite family gives the expected `Fin.cons`
description. -/
theorem cons_map_list_get_eq_fin_cons {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (r : A) (rs : List A) :
    ((r :: rs).map φ).get = Fin.cons (φ r) ((rs.map φ).get) := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the principal quotient module
`A / (r)` is canonically the same `A`-module as `QuotSMulTop r A`. -/
noncomputable def principal_quotient_linearEquiv_quotSMulTop
    {A : Type u} [CommRing A] (r : A) :
    QuotSMulTop r A ≃ₗ[A] A ⧸ Ideal.span ({r} : Set A) := by
  -- Proof comment: both sides are quotients of the regular module `A` by the same principal
  -- submodule, presented once as `r • ⊤` and once as `Ideal.span {r}`.
  refine Submodule.quotEquivOfEq _ _ ?_
  calc
    r • (⊤ : Submodule A A) = (Ideal.span ({r} : Set A) : Ideal A) • (⊤ : Submodule A A) := by
      simpa using (Submodule.ideal_span_singleton_smul r (⊤ : Submodule A A)).symm
    _ = (Ideal.span ({r} : Set A) : Ideal A) := by
      simpa using (Ideal.smul_top_eq_map (R := A) (S := A) (Ideal.span ({r} : Set A)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in positive degree, exactness of
the coefficient chain complex is equivalent to function exactness of the adjacent differentials. -/
theorem functionExact_of_exactAt_of_pos_degree {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat A) ℕ) {j : ℕ} (hj : 1 ≤ j) (h : K.ExactAt j) :
    Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): over `ModuleCat`, function
exactness of the underlying maps is exactly exactness of the short complex. -/
theorem shortComplex_exact_of_functionExact {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (h : Function.Exact S.f.hom S.g.hom) :
    S.Exact := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): exactness of a normalized short
complex transports back to exactness at the corresponding degree of the ambient chain complex. -/
theorem exactAt_of_sc_iso_exact {A : Type u} [CommRing A]
    {T : ChainComplex (ModuleCat A) ℕ} {i : ℕ} {S : ShortComplex (ModuleCat A)}
    (e : T.sc i ≅ S) (hS : S.Exact) :
    T.ExactAt i := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): exactness of an explicit
three-term `sc'` window transports back to exactness at the corresponding degree of the ambient
chain complex. -/
theorem exactAt_of_sc'_iso_exact {A : Type u} [CommRing A]
    {T : ChainComplex (ModuleCat A) ℕ} {i j k : ℕ} {S : ShortComplex (ModuleCat A)}
    (hi : (ComplexShape.down ℕ).prev j = i) (hk : (ComplexShape.down ℕ).next j = k)
    (e : T.sc' i j k ≅ S) (hS : S.Exact) :
    T.ExactAt j := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): every tensorized Koszul term
inherits `r`-regularity from the coefficient module, because the Koszul term is a finite free
module. -/
theorem isSMulRegular_tensor_koszul_term_of_isSMulRegular {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {r : A} {m : ℕ} (f : Fin m → A) (n : ℕ)
    (hr : IsSMulRegular M r) :
    IsSMulRegular
      (((HomologicalComplex.tensorObj (koszulComplexOn f)
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X n)) r := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): a class in `QuotSMulTop r M`
is zero exactly when its representative is an `r`-multiple. -/
theorem quotSMulTop_mk_eq_zero_iff_exists_smul {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {r : A} {x : M} :
    (Submodule.Quotient.mk x : QuotSMulTop r M) = 0 ↔ ∃ y : M, r • y = x := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): once the head/tail differential
has been normalized to the mapping-cone row
`(u, v) ↦ (d₂ u + r • v, - d₁ v)`, quotient exactness of `d₂, d₁` and `r`-regularity on the
target of `d₁` already give exactness of that row. -/
theorem functionExact_head_tail_row_of_quotient_exact_and_regular {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀} {d₀ : U₀ →ₗ[A] Uneg1}
    (hd₂₁ : d₁.comp d₂ = 0)
    (hd₁₀ : d₀.comp d₁ = 0)
    (hquot : Function.Exact (QuotSMulTop.map r d₂) (QuotSMulTop.map r d₁))
    (hreg : IsSMulRegular U₀ r) :
    Function.Exact
      (fun x : U₂ × U₁ ↦ (d₂ x.1 + r • x.2, - d₁ x.2))
      (fun y : U₁ × U₀ ↦ (d₁ y.1 + r • y.2, - d₀ y.2)) := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized incoming
head/tail row map in degree `i ≥ 2` on the tensor-side product model. -/
noncomputable def head_tail_row_left_map {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A} (d₂ : U₂ →ₗ[A] U₁) (d₁ : U₁ →ₗ[A] U₀) :
    (U₂ × U₁) →ₗ[A] (U₁ × U₀) :=
  (((d₂.comp (LinearMap.fst A U₂ U₁)) + r • (LinearMap.snd A U₂ U₁)).prod
    ((-d₁).comp (LinearMap.snd A U₂ U₁)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized outgoing
head/tail row map in degree `i ≥ 2` on the tensor-side product model. -/
noncomputable def head_tail_row_right_map {A : Type u} [CommRing A]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A} (d₁ : U₁ →ₗ[A] U₀) (d₀ : U₀ →ₗ[A] Uneg1) :
    (U₁ × U₀) →ₗ[A] (U₀ × Uneg1) :=
  (((d₁.comp (LinearMap.fst A U₁ U₀)) + r • (LinearMap.snd A U₁ U₀)).prod
    ((-d₀).comp (LinearMap.snd A U₁ U₀)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized outgoing low-row
map in degree `1` on the tensor-side product model. -/
noncomputable def head_tail_low_row_right_map {A : Type u} [CommRing A]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A} (d₁ : U₁ →ₗ[A] U₀) :
    (U₁ × U₀) →ₗ[A] U₀ :=
  (d₁.comp (LinearMap.fst A U₁ U₀)) + r • (LinearMap.snd A U₁ U₀)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the two normalized product-row
maps in degree `i ≥ 2` compose to zero whenever the tail differentials do. -/
theorem head_tail_row_maps_comp_zero {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀} {d₀ : U₀ →ₗ[A] Uneg1}
    (hd₂₁ : d₁.comp d₂ = 0) (hd₁₀ : d₀.comp d₁ = 0) :
    (head_tail_row_right_map (A := A) (r := r) d₁ d₀).comp
        (head_tail_row_left_map (A := A) (r := r) d₂ d₁) = 0 := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized product-row maps
in degree `1` compose to zero whenever the tail differential squares to zero. -/
theorem head_tail_low_row_maps_comp_zero {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀}
    (hd₂₁ : d₁.comp d₂ = 0) :
    (head_tail_low_row_right_map (A := A) (r := r) d₁).comp
        (head_tail_row_left_map (A := A) (r := r) d₂ d₁) = 0 := sorry

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized degree-`i ≥ 2`
mapping-cone row as a short complex in `ModuleCat`. -/
noncomputable def head_tail_row_shortComplex {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A}
    (d₂ : U₂ →ₗ[A] U₁) (d₁ : U₁ →ₗ[A] U₀) (d₀ : U₀ →ₗ[A] Uneg1)
    (hd₂₁ : d₁.comp d₂ = 0) (hd₁₀ : d₀.comp d₁ = 0) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (head_tail_row_left_map (A := A) (r := r) d₂ d₁))
    (ModuleCat.ofHom (head_tail_row_right_map (A := A) (r := r) d₁ d₀))
    (by
      change ModuleCat.ofHom
          ((head_tail_row_right_map (A := A) (r := r) d₁ d₀).comp
            (head_tail_row_left_map (A := A) (r := r) d₂ d₁)) = 0
      rw [head_tail_row_maps_comp_zero (A := A) (r := r) hd₂₁ hd₁₀]
      rfl)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized degree-`1`
mapping-cone row as a short complex in `ModuleCat`. -/
noncomputable def head_tail_low_row_shortComplex {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A}
    (d₂ : U₂ →ₗ[A] U₁) (d₁ : U₁ →ₗ[A] U₀)
    (hd₂₁ : d₁.comp d₂ = 0) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (head_tail_row_left_map (A := A) (r := r) d₂ d₁))
    (ModuleCat.ofHom (head_tail_low_row_right_map (A := A) (r := r) d₁))
    (by
      change ModuleCat.ofHom
          ((head_tail_low_row_right_map (A := A) (r := r) d₁).comp
            (head_tail_row_left_map (A := A) (r := r) d₂ d₁)) = 0
      rw [head_tail_low_row_maps_comp_zero (A := A) (r := r) hd₂₁]
      rfl)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in degree `1`, once the
head/tail differential is normalized to the low row
`(u, v) ↦ (d₂ u + r • v, - d₁ v)`, quotient exactness of `d₂, d₁` and `r`-regularity on the
target of `d₁` already give exactness of the truncated row. -/
theorem functionExact_head_tail_low_row_of_quotient_exact_and_regular {A : Type u}
    [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀}
    (hd₂₁ : d₁.comp d₂ = 0)
    (hquot : Function.Exact (QuotSMulTop.map r d₂) (QuotSMulTop.map r d₁))
    (hreg : IsSMulRegular U₀ r) :
    Function.Exact
      (fun x : U₂ × U₁ ↦ (d₂ x.1 + r • x.2, - d₁ x.2))
      (fun y : U₁ × U₀ ↦ d₁ y.1 + r • y.2) := sorry


end RingTheory.Sequence

@[stacks 061T "cons-family normalization"]
#check @RingTheory.Sequence.cons_list_get_eq_fin_cons
@[stacks 061T "mapped cons-family normalization"]
#check @RingTheory.Sequence.cons_map_list_get_eq_fin_cons
@[stacks 061T "principal quotient comparison"]
#check @RingTheory.Sequence.principal_quotient_linearEquiv_quotSMulTop
@[stacks 061T "positive-degree exactness"]
#check @RingTheory.Sequence.functionExact_of_exactAt_of_pos_degree
@[stacks 061T "short-complex exactness"]
#check @RingTheory.Sequence.shortComplex_exact_of_functionExact
@[stacks 061T "exactness transport across a short-complex isomorphism"]
#check @RingTheory.Sequence.exactAt_of_sc_iso_exact
@[stacks 061T "exactness transport across an explicit three-term window"]
#check @RingTheory.Sequence.exactAt_of_sc'_iso_exact
@[stacks 061T "regularity on tensorized Koszul terms"]
#check @RingTheory.Sequence.isSMulRegular_tensor_koszul_term_of_isSMulRegular
@[stacks 061T "principal quotient vanishing criterion"]
#check @RingTheory.Sequence.quotSMulTop_mk_eq_zero_iff_exists_smul
@[stacks 061T "head-tail row exactness criterion"]
#check @RingTheory.Sequence.functionExact_head_tail_row_of_quotient_exact_and_regular
@[stacks 061T "head-tail incoming row map"]
#check @RingTheory.Sequence.head_tail_row_left_map
@[stacks 061T "head-tail outgoing row map"]
#check @RingTheory.Sequence.head_tail_row_right_map
@[stacks 061T "head-tail low-row map"]
#check @RingTheory.Sequence.head_tail_low_row_right_map
@[stacks 061T "head-tail row differential squares to zero"]
#check @RingTheory.Sequence.head_tail_row_maps_comp_zero
@[stacks 061T "head-tail low-row differential squares to zero"]
#check @RingTheory.Sequence.head_tail_low_row_maps_comp_zero
@[stacks 061T "head-tail short complex"]
#check @RingTheory.Sequence.head_tail_row_shortComplex
@[stacks 061T "head-tail low-row short complex"]
#check @RingTheory.Sequence.head_tail_low_row_shortComplex
@[stacks 061T "head-tail low-row exactness criterion"]
#check @RingTheory.Sequence.functionExact_head_tail_low_row_of_quotient_exact_and_regular
