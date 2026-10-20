/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Uniqueness
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Henselian

@[expose] public section

/-! # Endomorphism rings of simple modules

This file establishes properties of endomorphism rings of simple modules over simple
Artinian algebras: invertibility of nonzero endomorphisms (Schur's lemma),
finite-dimensionality, center equivalence, the dimension formula, and the matrix
description for finite modules.
-/

universe u v w w' w''

section MatrixModel

open scoped Matrix.Module

variable {K : Type v} [DivisionRing K]
variable {n : ℕ}

private noncomputable def endSelfToMatrixModuleEnd :
    Module.End K K →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun f := LinearMap.mapMatrixModule (Fin n) f
  map_one' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_mul' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_zero' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_add' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]

private noncomputable def scalarToMatrixModuleEnd :
    Kᵐᵒᵖ →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  endSelfToMatrixModuleEnd.comp (RingEquiv.moduleEndSelf K).toRingHom

private theorem scalarToMatrixModuleEnd_apply (x : Kᵐᵒᵖ) (v : Fin n → K) :
    scalarToMatrixModuleEnd x v = fun i ↦ v i * MulOpposite.unop x := by
  ext i
  simp [scalarToMatrixModuleEnd, endSelfToMatrixModuleEnd, LinearMap.mapMatrixModule_apply]

private noncomputable def matrixModuleEndScalar (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) : K :=
  f (Pi.single ⟨0, hn⟩ (1 : K)) ⟨0, hn⟩

private theorem matrixModuleEnd_basis_eq (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    ∀ i : Fin n,
      f (Pi.single i (1 : K)) = Pi.single i (matrixModuleEndScalar hn f) := by
  let i0 : Fin n := ⟨0, hn⟩
  have h0 : f (Pi.single i0 (1 : K)) = Pi.single i0 (matrixModuleEndScalar hn f) := by
    simpa [matrixModuleEndScalar, i0, Matrix.Module.single_smul] using
      (f.map_smul (Matrix.single i0 i0 (1 : K)) (Pi.single i0 (1 : K)))
  intro i
  simpa [i0, h0, Matrix.Module.single_smul] using
    (f.map_smul (Matrix.single i i0 (1 : K)) (Pi.single i0 (1 : K)))

private theorem scalarToMatrixModuleEnd_left_inv (hn : 1 ≤ n) (x : Kᵐᵒᵖ) :
    matrixModuleEndScalar hn (scalarToMatrixModuleEnd x) = MulOpposite.unop x := by
  simp [matrixModuleEndScalar, scalarToMatrixModuleEnd_apply]

private theorem scalarToMatrixModuleEnd_right_inv (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    scalarToMatrixModuleEnd (MulOpposite.op (matrixModuleEndScalar hn f)) = f := by
  ext v i
  have hbasis := matrixModuleEnd_basis_eq hn f
  have hv : v = ∑ j : Fin n, v j • (Pi.single j (1 : K) : Fin n → K) := by
    ext j
    simp [Pi.single_apply]
  have hfv : f v = ∑ j : Fin n, v j • f (Pi.single j (1 : K)) := by
    ext i
    rw [hv, map_sum]
    simp [Pi.single_apply, f.map_smul_of_tower]
  calc
    scalarToMatrixModuleEnd (MulOpposite.op (matrixModuleEndScalar hn f)) v i
        = (fun j ↦ v j * matrixModuleEndScalar hn f) i := by
            simp [scalarToMatrixModuleEnd_apply]
    _ = (f v) i := by
      rw [hfv]
      simp [hbasis, Pi.single_apply]

private noncomputable def scalarToMatrixModuleEndEquiv (hn : 1 ≤ n) :
    Kᵐᵒᵖ ≃+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun := scalarToMatrixModuleEnd
  invFun f := MulOpposite.op (matrixModuleEndScalar hn f)
  left_inv x := by
    apply MulOpposite.unop_injective
    exact scalarToMatrixModuleEnd_left_inv hn x
  right_inv := scalarToMatrixModuleEnd_right_inv hn
  map_mul' := scalarToMatrixModuleEnd.map_mul
  map_add' := scalarToMatrixModuleEnd.map_add

section

variable {k : Type u} [Field k] [Algebra k K]

private noncomputable def endSelfToMatrixModuleEndAlgHom :
    Module.End K K →ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun f := LinearMap.mapMatrixModule (Fin n) f
  map_one' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_mul' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_zero' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_add' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  commutes' c := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply, Algebra.algebraMap_eq_smul_one]

private noncomputable def scalarToMatrixModuleEndAlgHom :
    Kᵐᵒᵖ →ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  endSelfToMatrixModuleEndAlgHom.comp
    (AlgEquiv.moduleEndSelf k : Kᵐᵒᵖ ≃ₐ[k] Module.End K K).toAlgHom

private noncomputable def scalarToMatrixModuleEndAlgEquiv (hn : 1 ≤ n) :
    Kᵐᵒᵖ ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  AlgEquiv.ofRingEquiv (f := scalarToMatrixModuleEndEquiv hn)
    (fun c ↦ scalarToMatrixModuleEndAlgHom.commutes c)
/-- For the standard simple module over `Matrix (Fin n) (Fin n) K`, the
endomorphism ring is `k`-algebra isomorphic to `Kᵐᵒᵖ`. -/
@[stacks 074E, no_expose]
noncomputable def matrix_endomorphism_alg_equiv_op (hn : 1 ≤ n) :
    Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ :=
  (scalarToMatrixModuleEndAlgEquiv hn).symm

/-- Read the right-multiplication scalar from the first standard basis vector. -/
@[simp]
theorem matrix_endomorphism_alg_equiv_op_apply (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    matrix_endomorphism_alg_equiv_op (k := k) hn f =
      MulOpposite.op (f (Pi.single ⟨0, hn⟩ (1 : K)) ⟨0, hn⟩) := by
  rfl

/-- A scalar in the opposite ring acts on every vector coordinate on the right. -/
@[simp]
theorem matrix_endomorphism_alg_equiv_op_symm_apply (hn : 1 ≤ n)
    (x : Kᵐᵒᵖ) (v : Fin n → K) :
    (matrix_endomorphism_alg_equiv_op (k := k) hn).symm x v =
      fun i ↦ v i * MulOpposite.unop x :=
  scalarToMatrixModuleEnd_apply x v

end

end MatrixModel

section SimpleModuleEndomorphisms

open Module.End

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]

namespace IsSimpleModule

/-- If `M` is a simple left `A`-module, then every nonzero `A`-endomorphism of
`M` is a unit, so `Module.End A M` is a skew field. -/
@[stacks 074E]
theorem end_isUnit_of_ne_zero
    {A : Type v} {M : Type w} [Ring A] [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    (f : Module.End A M) (hf : f ≠ 0) :
    IsUnit f := by
  exact (Module.End.isUnit_iff f).2 (f.bijective_of_ne_zero hf)

variable [Module k M] [IsScalarTower k A M]

omit [IsSimpleRing A] in
/-- For a simple left `A`-module `M`, the endomorphism skew field
`Module.End A M` is finite-dimensional over `k`. -/
@[stacks 074E]
theorem finiteDimensional_end :
    FiniteDimensional k (Module.End A M) := by
  let _ : FiniteDimensional k M :=
    IsSimpleModule.finiteDimensional (k := k) (A := A) (M := M)
  let forgetEnd :
      Module.End A M →ₗ[k] Module.End k M :=
    { toFun := fun f ↦
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun c x ↦ by
            simpa [Algebra.smul_def] using f.map_smul ((algebraMap k A) c) x }
      map_add' := fun f g ↦ rfl
      map_smul' := fun c f ↦ rfl }
  have hforget : Function.Injective forgetEnd := by
    intro f g hfg
    ext x
    exact congrArg (fun h : Module.End k M ↦ h x) hfg
  exact FiniteDimensional.of_injective forgetEnd hforget

end IsSimpleModule

def centerToModuleEndCenter
    (R : Type v) (M : Type w) [DivisionRing R] [AddCommGroup M] [Module R M] :
    Subring.center R →+* Subring.center (Module.End R M) where
  toFun z := by
    let hz : (z : R) ∈ Set.center R := by
      rw [Semigroup.mem_center_iff]
      exact Subring.mem_center_iff.mp z.2
    exact ⟨Module.End.smulLeft z.1 hz, by
      change Module.End.smulLeft z.1 hz ∈ Set.center (Module.End R M)
      exact (Module.End.mem_center_iff).2 ⟨z.1, hz, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    ext m
    change (1 : R) • m = m
    simp
  map_mul' x y := by
    apply Subtype.ext
    ext m
    change ((x : R) * (y : R)) • m = (x : R) • ((y : R) • m)
    simp [mul_smul]
  map_zero' := by
    apply Subtype.ext
    ext m
    change (0 : R) • m = 0
    simp
  map_add' x y := by
    apply Subtype.ext
    ext m
    change ((x : R) + (y : R)) • m = (x : R) • m + (y : R) • m
    simp [add_smul]

noncomputable def centerModuleEndEquiv
    (R : Type v) (M : Type w) [DivisionRing R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    Subring.center R ≃+* Subring.center (Module.End R M) :=
  RingEquiv.ofBijective (centerToModuleEndCenter R M) <| by
    constructor
    · intro x y hxy
      apply Subtype.ext
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      exact smul_left_injective R hm <| by
        exact congrArg (fun z : Subring.center (Module.End R M) ↦ z.1 m) hxy
    · intro f
      have hf : (f : Module.End R M) ∈ Set.center (Module.End R M) := by
        rw [Semigroup.mem_center_iff]
        exact Subring.mem_center_iff.mp f.2
      rcases (Module.End.mem_center_iff).1 hf with ⟨r, hr, hfr⟩
      refine ⟨⟨r, by
        rw [Subring.mem_center_iff]
        exact Semigroup.mem_center_iff.mp hr⟩, ?_⟩
      apply Subtype.ext
      simpa [centerToModuleEndCenter] using hfr.symm

theorem simple_module_moduleFinite_over_end'
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

noncomputable def module_double_centralizer_of_finite_end'
    (A : Type v) (M : Type w) [Ring A] [IsSimpleRing A] [AddCommGroup M] [Module A M]
    [Nontrivial M] [IsSemisimpleModule A M] [Module.Finite (Module.End A M) M] :
    A ≃+* Module.End (Module.End A M) M :=
  RingEquiv.ofBijective (Module.toModuleEnd (Module.End A M) M)
    ⟨RingHom.injective _, Module.Finite.toModuleEnd_moduleEnd_surjective⟩

namespace IsSimpleModule

/-- The centers of `A` and `Module.End A M` are canonically ring-isomorphic. -/
@[stacks 074E]
noncomputable def centerEquiv
    {k : Type u} {A : Type v} {M : Type w}
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [IsArtinianRing A] :
    Subring.center A ≃+* Subring.center (Module.End A M) := by
  classical
  let _ : Nontrivial M := IsSimpleModule.nontrivial A M
  let _ : DecidableEq (Module.End A M) := Classical.decEq _
  let _ : DivisionRing (Module.End A M) := Module.End.instDivisionRing
  let _ : IsSemisimpleRing A := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let _ : Module.Finite (Module.End A M) M := simple_module_moduleFinite_over_end' A M
  let e : A ≃+* Module.End (Module.End A M) M :=
    module_double_centralizer_of_finite_end' A M
  exact (Subring.centerCongr e).trans <|
    (centerModuleEndEquiv (Module.End A M) M).symm

end IsSimpleModule

section FiniteFunctionRanks

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
private theorem fin_succ_fun_nonempty_linearEquiv (n : ℕ) :
    Nonempty ((Fin (n + 1) → V) ≃ₗ[k] V × (Fin n → V)) := by
  refine ⟨?_⟩
  refine
    { toFun := fun f ↦ (f 0, fun i ↦ f i.succ)
      invFun := fun p i ↦ Fin.cases p.1 p.2 i
      map_add' := fun f g ↦ rfl
      map_smul' := fun c f ↦ rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    ext i
    cases i using Fin.cases with
    | zero =>
        rfl
    | succ i =>
        rfl
  · intro p
    rcases p with ⟨x, f⟩
    rfl

private theorem finrank_fin_fun (n : ℕ) :
    Module.finrank k (Fin n → V) = n * Module.finrank k V := by
  induction n with
  | zero =>
      simp [Module.finrank_pi_fintype]
  | succ n ih =>
      obtain ⟨e⟩ := fin_succ_fun_nonempty_linearEquiv (k := k) (V := V) n
      calc
        Module.finrank k (Fin (n + 1) → V) = Module.finrank k (V × (Fin n → V)) :=
          e.finrank_eq
        _ = Module.finrank k V + Module.finrank k (Fin n → V) := Module.finrank_prod
        _ = Module.finrank k V + n * Module.finrank k V := by rw [ih]
        _ = n * Module.finrank k V + Module.finrank k V := by rw [Nat.add_comm]
        _ = (n + 1) * Module.finrank k V := by rw [Nat.add_mul, one_mul]

end FiniteFunctionRanks

namespace IsSimpleModule

section

open Module.End
open scoped Matrix.Module

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]
variable [Module k M] [IsScalarTower k A M]

/-- If `M` is a simple left `A`-module and `L = Module.End A M`, then
`[A : k] * [L : k] = dim_k(M)^2`. -/
@[stacks 074E]
theorem finrank_mul_finrank_end :
    Module.finrank k A * Module.finrank k (Module.End A M) = (Module.finrank k M) ^ 2 := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn0, K, hKdiv, hKalg, hKfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn0
  letI : DivisionRing K := hKdiv
  letI : Algebra k K := hKalg
  letI : Module.Finite k K := hKfin
  letI : FiniteDimensional k K := inferInstance
  let hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  letI : Module A (Fin n → K) := Module.compHom (Fin n → K) e.toRingHom
  letI : Module k (Fin n → K) := inferInstance
  letI : IsScalarTower k A (Fin n → K) := by
    refine ⟨?_⟩
    intro c a x
    calc
      e (c • a) • x = (c • e a) • x := by
        congr 1
        simpa [Algebra.smul_def] using
          (show e (((algebraMap k A) c) * a) =
              ((algebraMap k (Matrix (Fin n) (Fin n) K)) c) * e a from
            e.map_mul ((algebraMap k A) c) a)
      _ = c • (e a • x) := smul_assoc c (e a) x
  letI : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let compLinearMap : (Fin n → K) →ₛₗ[e.toRingHom] (Fin n → K) :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  letI : IsSimpleModule A (Fin n → K) :=
    (LinearMap.isSimpleModule_iff_of_bijective compLinearMap Function.bijective_id).2
      (IsSimpleModule.matrix_fin_fun hn)
  let l : M ≃ₗ[A] (Fin n → K) := IsSimpleModule.nonempty_linearEquiv.some
  let eComp :
      Module.End A (Fin n → K) ≃ₐ[k]
        Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) := by
    refine
      { toFun := fun f ↦
          { toFun := f
            map_add' := f.map_add
            map_smul' := by
              intro b x
              obtain ⟨a, rfl⟩ := e.surjective b
              exact f.map_smul a x }
        invFun := fun f ↦
          { toFun := f
            map_add' := f.map_add
            map_smul' := fun a x ↦ f.map_smul (e a) x }
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl
        map_mul' := by intro f g; rfl
        map_add' := by intro f g; rfl
        commutes' := by
          intro c
          ext x
          simp [Algebra.algebraMap_eq_smul_one] }
  let eK :
      Module.End A (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ :=
    eComp.trans (matrix_endomorphism_alg_equiv_op hn)
  let hop : Module.End A M ≃ₐ[k] Kᵐᵒᵖ :=
    (l.conjAlgEquiv k).trans eK
  have hA :
      Module.finrank k A = n * n * Module.finrank k K := by
    calc
      Module.finrank k A = Module.finrank k (Matrix (Fin n) (Fin n) K) :=
        e.toLinearEquiv.finrank_eq
      _ = n * n * Module.finrank k K := by
        simpa using (Module.finrank_matrix k K (Fin n) (Fin n))
  have hM :
      Module.finrank k M = n * Module.finrank k K := by
    calc
      Module.finrank k M = Module.finrank k (Fin n → K) :=
        (l.restrictScalars k).finrank_eq
      _ = n * Module.finrank k K := finrank_fin_fun (k := k) (V := K) n
  have hEnd :
      Module.finrank k (Module.End A M) = Module.finrank k K := by
    calc
      Module.finrank k (Module.End A M) = Module.finrank k Kᵐᵒᵖ :=
        hop.toLinearEquiv.finrank_eq
      _ = Module.finrank k K := by
        simpa using
          (LinearEquiv.finrank_eq (MulOpposite.opLinearEquiv k : K ≃ₗ[k] Kᵐᵒᵖ)).symm
  calc
    Module.finrank k A * Module.finrank k (Module.End A M)
        = (n * n * Module.finrank k K) * Module.finrank k K := by rw [hA, hEnd]
    _ = (n * Module.finrank k K) ^ 2 := by
      simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (Module.finrank k M) ^ 2 := by rw [hM]

end

section FiniteModuleEndomorphisms

variable {k : Type u} {A : Type v} {M : Type w} {N : Type w'}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]
variable [AddCommGroup N] [Module A N] [Module.Finite A N]
variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

private theorem nonempty_linearEquiv_fin_fun'
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [Module.Finite A N] :
    ∃ n : ℕ, Nonempty (N ≃ₗ[A] (Fin n → M)) := by
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let hNM : IsIsotypicOfType A N M := fun S _ ↦ by
    let _ : IsSimpleModule A S := ‹_›
    exact IsSimpleModule.nonempty_linearEquiv
  exact hNM.linearEquiv_fun

/-- For a finite left `A`-module `N`, the endomorphism ring `Module.End A N`
is `k`-algebra isomorphic to a matrix algebra over the skew field `Module.End A M`, where `M` is
any simple left `A`-module. -/
@[stacks 074E]
theorem end_algEquiv_matrix :
    ∃ n : ℕ, Nonempty (Module.End A N ≃ₐ[k] Matrix (Fin n) (Fin n) (Module.End A M)) := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, ⟨e⟩⟩ :=
    nonempty_linearEquiv_fin_fun' (A := A) (M := M) (N := N)
  refine ⟨n, ?_⟩
  exact ⟨(e.conjAlgEquiv k).trans (endVecAlgEquivMatrixEnd (Fin n) k A M)⟩

end FiniteModuleEndomorphisms

end IsSimpleModule

end SimpleModuleEndomorphisms

end
