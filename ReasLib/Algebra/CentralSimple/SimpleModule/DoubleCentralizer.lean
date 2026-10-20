/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Endomorphism
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

/-! # Double centralizer theorems

This file establishes the double centralizer (bicommutant) theorems for simple modules
over simple Artinian rings, both in the ring-theoretic and algebra-theoretic forms, as
well as the classical bicommutant theorem for right ideals of simple rings.
-/

universe u v w w'

namespace IsSimpleModule

section

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]

theorem moduleFinite_over_end
    (A : Type v) (M : Type w)
    [Ring A] [IsSimpleRing A] [IsArtinianRing A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.Finite (Module.End A M) M := by
  let hA : IsIsotypic A A := IsSimpleRing.isIsotypic A A
  obtain ⟨n, _, S, _hS, ⟨e⟩⟩ := hA.linearEquiv_fun
  have hSM : Nonempty (S ≃ₗ[A] M) := IsSimpleModule.nonempty_linearEquiv
  let eSM : S ≃ₗ[A] M := hSM.some
  let e' : A ≃ₗ[A] Fin n → M := e.trans <| .piCongrRight fun _ ↦ eSM
  let v : Fin n → M := e' (1 : A)
  have hspan : Submodule.span (Module.End A M) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let p : A →ₗ[A] M :=
      { toFun := fun a ↦ a • x
        map_add' := fun _ _ ↦ by simp [add_smul]
        map_smul' := fun a b ↦ by simp [mul_smul] }
    let g : (Fin n → M) →ₗ[A] M := p.comp e'.symm.toLinearMap
    refine (Submodule.mem_span_range_iff_exists_fun (Module.End A M)).2 ?_
    refine ⟨fun i ↦ g.comp (LinearMap.single A (fun _ : Fin n ↦ M) i), ?_⟩
    calc
      ∑ i, (g.comp (LinearMap.single A (fun _ : Fin n ↦ M) i) : Module.End A M) • v i
          = ∑ i, g (Pi.single i (v i)) := by
              simp [LinearMap.comp_apply]
      _ = g (∑ i, Pi.single i (v i)) := by rw [map_sum]
      _ = g (e' (1 : A)) := by
            congr
            ext i
            simp [v]
      _ = x := by simp [g, p]
  let _ : Module.Finite (Module.End A M) (Fin n → Module.End A M) :=
    Module.Finite.of_basis (Pi.basisFun (Module.End A M) (Fin n))
  exact Module.Finite.of_surjective
    (Fintype.linearCombination (Module.End A M) v)
    ((span_range_eq_top_iff_surjective_fintypeLinearCombination (Module.End A M) v).1
      hspan)

noncomputable def doubleCentralizerRingEquiv
    (A : Type v) (M : Type w) [Ring A] [IsSimpleRing A] [AddCommGroup M] [Module A M]
    [Nontrivial M] [IsSemisimpleModule A M] [Module.Finite (Module.End A M) M] :
    A ≃+* Module.End (Module.End A M) M :=
  RingEquiv.ofBijective (Module.toModuleEnd (Module.End A M) M)
    ⟨RingHom.injective _, Module.Finite.toModuleEnd_moduleEnd_surjective⟩

/-- For a simple left module over a simple Artinian ring, the bicommutant
recovers the original ring as a `k`-algebra equivalence. -/
@[stacks 074E]
noncomputable def doubleCentralizerAlgEquiv [Module k M] [IsScalarTower k A M] :
    A ≃ₐ[k] Module.End (Module.End A M) M :=
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let _ : Nontrivial M := IsSimpleModule.nontrivial A M
  let _ : IsSemisimpleRing A := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let _ : Module.Finite (Module.End A M) M := moduleFinite_over_end A M
  let e : A ≃+* Module.End (Module.End A M) M := doubleCentralizerRingEquiv A M
  { __ := e
    commutes' c := by
      ext m
      simp [e, doubleCentralizerRingEquiv, Algebra.algebraMap_eq_smul_one] }

end

section FiniteModule

variable {k : Type u} {A : Type v} {M : Type w} {N : Type w'}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]
variable [AddCommGroup N] [Module A N] [Module.Finite A N]
variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

/-- For a nonzero finite left `A`-module `N`, the bicommutant of `N` recovers
the original algebra `A`. -/
@[stacks 074E]
noncomputable def doubleCentralizerAlgEquiv_finite [Nontrivial N] :
    A ≃ₐ[k] Module.End (Module.End A N) N :=
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr (IsArtinianRing.of_finite k A)
  let _ : Module.Finite k N := Module.Finite.trans A N
  let _ : Module.Finite (Module.End A N) N :=
    Module.Finite.of_restrictScalars_finite k (Module.End A N) N
  let e : A ≃+* Module.End (Module.End A N) N := doubleCentralizerRingEquiv A N
  { __ := e
    commutes' c := by
      ext n
      simp [e, doubleCentralizerRingEquiv, Algebra.algebraMap_eq_smul_one] }

end FiniteModule

end IsSimpleModule

namespace IsSimpleRing

section

open Module (End toModuleEnd)
open scoped BigOperators

variable {A : Type u} [Ring A] [IsSimpleRing A]

private lemma rightIdeal_left_mul_mem {M : Submodule Aᵐᵒᵖ A} (m x : M) :
    ((m : A) * x : A) ∈ M := by
  simpa using M.smul_mem (MulOpposite.op (x : A)) m.property

private lemma rightIdeal_mul_right_mem {M : Submodule Aᵐᵒᵖ A} (x : M) (a : A) :
    ((x : A) * a : A) ∈ M := by
  simpa using M.smul_mem (MulOpposite.op a) x.property

private lemma rightIdeal_span_mul_mem {M : Submodule Aᵐᵒᵖ A} {x : A}
    (hx : x ∈ Ideal.span (M : Set A)) (a : A) :
    x * a ∈ Ideal.span (M : Set A) := by
  refine Submodule.span_induction (p := fun y _ ↦ y * a ∈ Ideal.span (M : Set A)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Ideal.subset_span (rightIdeal_mul_right_mem ⟨y, hy⟩ a)
  · simpa using (Ideal.zero_mem (Ideal.span (M : Set A)))
  · intro y z _ _ hy hz
    simpa [add_mul] using Ideal.add_mem (Ideal.span (M : Set A)) hy hz
  · intro b y _ hy
    simpa [smul_eq_mul, mul_assoc] using Ideal.mul_mem_left (Ideal.span (M : Set A)) b hy

private lemma rightIdeal_span_isTwoSided (M : Submodule Aᵐᵒᵖ A) :
    (Ideal.span (M : Set A)).IsTwoSided := by
  refine Ideal.IsTwoSided.mk ?_
  intro x a hx
  exact rightIdeal_span_mul_mem hx a

private lemma left_mul_endomorphism_map_add {M : Submodule Aᵐᵒᵖ A} (m : M) :
    ∀ x y : M,
      (⟨(m : A) * (x + y), rightIdeal_left_mul_mem m (x + y)⟩ : M) =
        ⟨(m : A) * x, rightIdeal_left_mul_mem m x⟩ +
          ⟨(m : A) * y, rightIdeal_left_mul_mem m y⟩ := by
  intro x y
  apply Subtype.ext
  simp [mul_add]

private lemma left_mul_endomorphism_map_smul {M : Submodule Aᵐᵒᵖ A} (m : M) :
    ∀ (a : Aᵐᵒᵖ) (x : M),
      (⟨(m : A) * (a • x : M), rightIdeal_left_mul_mem m (a • x : M)⟩ : M) =
        a • ⟨(m : A) * x, rightIdeal_left_mul_mem m x⟩ := by
  intro a x
  cases a
  apply Subtype.ext
  simp [mul_assoc]

private def left_mul_endomorphism {M : Submodule Aᵐᵒᵖ A} (m : M) : End Aᵐᵒᵖ M :=
  { toFun := fun x ↦ ⟨(m : A) * x, rightIdeal_left_mul_mem m x⟩
    map_add' := left_mul_endomorphism_map_add m
    map_smul' := left_mul_endomorphism_map_smul m }

private def finset_rightIdeal_member {M : Submodule Aᵐᵒᵖ A} {s : Finset A}
    (hs : ↑s ⊆ (M : Set A)) (m : {x // x ∈ s}) : M :=
  ⟨m.1, hs m.2⟩

private def scaled_rightIdeal_member {M : Submodule Aᵐᵒᵖ A} (x : M) (a : A) : M :=
  ⟨(x : A) * a, rightIdeal_mul_right_mem x a⟩

private lemma bicommutant_map_left_mul {M : Submodule Aᵐᵒᵖ A} (f : End (End Aᵐᵒᵖ M) M)
    (m x : M) :
    f (left_mul_endomorphism m x) = left_mul_endomorphism m (f x) := by
  simpa [Module.End.smul_def] using f.map_smul (left_mul_endomorphism m) x

private lemma rightIdeal_span_eq_top_of_nonzero (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Ideal.span (M : Set A) = ⊤ := by
  let J : Ideal A := Ideal.span (M : Set A)
  have hJ_ne : J ≠ ⊥ := by
    obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff _).mp hM
    have hmJ : m ∈ J := Ideal.subset_span hmM
    intro hJ
    have hmBot : m ∈ (⊥ : Ideal A) := by
      simpa [J, hJ] using hmJ
    exact hm0 (by simpa using hmBot)
  letI : J.IsTwoSided := by
    simpa [J] using rightIdeal_span_isTwoSided M
  rcases IsSimpleRing.simple.eq_bot_or_eq_top J.toTwoSided with hJ | hJ
  · have hJ' : J = ⊥ := by
      simpa [J] using congrArg TwoSidedIdeal.asIdeal hJ
    exact (hJ_ne hJ').elim
  · simpa [J] using congrArg TwoSidedIdeal.asIdeal hJ

private lemma exists_unit_relation_of_nonzero_right_ideal (M : Submodule Aᵐᵒᵖ A)
    (hM : M ≠ ⊥) :
    ∃ s : Finset A, ↑s ⊆ (M : Set A) ∧
      ∃ c : A → A, Finset.sum s (fun m ↦ c m * m) = 1 := by
  have hspan : Ideal.span (M : Set A) = ⊤ := rightIdeal_span_eq_top_of_nonzero M hM
  obtain ⟨s, hs, hsTop⟩ := (Ideal.span_eq_top_iff_finite (M : Set A)).mp hspan
  have hOne : (1 : A) ∈ Ideal.span (s : Set A) := by
    simpa [Ideal.eq_top_iff_one] using hsTop
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hOne
  exact ⟨s, hs, c, by simpa [smul_eq_mul] using hc⟩

private lemma bicommutant_reconstruct_of_unit_relation {M : Submodule Aᵐᵒᵖ A}
    (f : End (End Aᵐᵒᵖ M) M) (s : Finset A) (hs : ↑s ⊆ (M : Set A)) (c : A → A)
    (hc : Finset.sum s (fun m ↦ c m * m) = 1) :
    let a := Finset.sum s.attach (fun m ↦ c m.1 * (f (finset_rightIdeal_member hs m) : A))
    ∀ x : M, (f x : A) = (x : A) * a := by
  intro a x
  have hx_decomp :
      x =
        Finset.sum s.attach
          (fun m ↦
            left_mul_endomorphism (scaled_rightIdeal_member x (c m.1))
              (finset_rightIdeal_member hs m)) := by
    have hx_val :
        (x : A) = Finset.sum s.attach (fun m ↦ (((x : A) * c m.1) * m.1)) := by
      calc
        (x : A) = (x : A) * 1 := by simp
        _ = (x : A) * Finset.sum s (fun m ↦ c m * m) := by rw [hc]
        _ = Finset.sum s (fun m ↦ (x : A) * (c m * m)) := by rw [Finset.mul_sum]
        _ = Finset.sum s (fun m ↦ ((x : A) * c m) * m) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [mul_assoc]
        _ = Finset.sum s.attach (fun m ↦ (((x : A) * c m.1) * m.1)) := by
              simpa using (Finset.sum_attach s (fun m : A ↦ ((x : A) * c m) * m)).symm
    exact Subtype.ext (by
      simpa [left_mul_endomorphism, scaled_rightIdeal_member, finset_rightIdeal_member] using
        hx_val)
  have hsum_apply :
      (f x : A) =
        Finset.sum s.attach
          (fun m ↦
            (f
              (left_mul_endomorphism (scaled_rightIdeal_member x (c m.1))
                (finset_rightIdeal_member hs m)) : A)) := by
    simpa [map_sum] using congrArg Subtype.val (congrArg f hx_decomp)
  calc
    (f x : A)
        = Finset.sum s.attach
            (fun m ↦
              (f
                (left_mul_endomorphism (scaled_rightIdeal_member x (c m.1))
                  (finset_rightIdeal_member hs m)) : A)) := hsum_apply
    _ = Finset.sum s.attach
          (fun m ↦ (((x : A) * c m.1) * (f (finset_rightIdeal_member hs m) : A))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            exact congrArg Subtype.val
              (bicommutant_map_left_mul f (scaled_rightIdeal_member x (c m.1))
                (finset_rightIdeal_member hs m))
    _ = Finset.sum s.attach
          (fun m ↦ (x : A) * (c m.1 * (f (finset_rightIdeal_member hs m) : A))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [mul_assoc]
    _ = (x : A) *
          Finset.sum s.attach
            (fun m ↦ c m.1 * (f (finset_rightIdeal_member hs m) : A)) := by
            rw [← Finset.mul_sum]
    _ = (x : A) * a := by
            rfl

private lemma rightIdeal_bicommutant_surjective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Surjective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* End (End Aᵐᵒᵖ M) M) := by
  intro f
  obtain ⟨s, hs, c, hc⟩ := exists_unit_relation_of_nonzero_right_ideal M hM
  let a : A := Finset.sum s.attach
    (fun m ↦ c m.1 * (f (finset_rightIdeal_member hs m) : A))
  refine ⟨MulOpposite.op a, ?_⟩
  ext x
  have := (bicommutant_reconstruct_of_unit_relation (M := M) (f := f) (s := s) (hs := hs) (c := c)
      (hc := hc) x).symm
  simp only [a] at this ⊢
  exact this

/-- If `A` is a simple ring and `M` is a nonzero right ideal of `A`, then the
canonical right-multiplication map from `Aᵐᵒᵖ` to the bicommutant
`End (End Aᵐᵒᵖ M) M` is bijective. -/
theorem bicommutant_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _) := by
  have hNontrivialM : Nontrivial M := by
    obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff _).mp hM
    refine ⟨⟨0, M.zero_mem⟩, ⟨m, hmM⟩, ?_⟩
    intro hEq
    exact hm0 (congrArg Subtype.val hEq).symm
  let _ : Nontrivial M := hNontrivialM
  exact ⟨RingHom.injective _, rightIdeal_bicommutant_surjective M hM⟩

/-- The bicommutant of a nonzero right ideal of a simple ring recovers the
original opposite ring. -/
noncomputable def doubleCentralizerRingEquiv (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Aᵐᵒᵖ ≃+* End (End Aᵐᵒᵖ M) M :=
  RingEquiv.ofBijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _)
    (bicommutant_bijective M hM)

end

end IsSimpleRing

end
