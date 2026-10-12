/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import ReasLib.Algebra.CentralSimple.SimpleModule.Uniqueness
public import ReasLib.Algebra.CentralSimple.SimpleModule.Endomorphism

/-! # Division Algebra Representatives of Brauer Classes

Every Brauer class has a division algebra representative, and two finite-dimensional
central division algebras represent the same class if and only if they are isomorphic.

## Main declarations

- `CSA.exists_divisionAlgebra_brauerEquivalent` — existence of division representative
- `CSA.brauerEquivalent_divisionAlgebra_iff` — uniqueness criterion

## References

- [Stacks Project, Tag 074K](https://stacks.math.columbia.edu/tag/074K)
-/

@[expose] public section

open Matrix
open scoped Matrix.Module

universe u v

section

variable (k : Type u) [Field k]
variable (A : CSA.{u, v} k)

private theorem isCentral_of_matrix (n : ℕ) [NeZero n] (D : Type v) [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) D)] : Algebra.IsCentral k D where
  out x hx := by
    have hxM : scalar (Fin n) x ∈ (Subalgebra.center k D).map (scalarAlgHom (Fin n) k) := by
      exact ⟨x, hx, rfl⟩
    rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
    rw [Algebra.mem_bot]
    refine ⟨a, ?_⟩
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    have := congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha
    simp [Matrix.scalar_apply, i] at this
    exact this.symm

/-- Every finite-dimensional central simple `k`-algebra is Brauer equivalent to one
attached to a finite-dimensional central division `k`-algebra. -/
lemma exists_divisionAlgebra_brauerEquivalent :
    ∃ (K : Type v) (_ : DivisionRing K) (_ : Algebra k K) (_ : Algebra.IsCentral k K)
      (_ : FiniteDimensional k K),
      IsBrauerEquivalent A (CSA.mk (AlgCat.of k K)) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, K, hKdiv, hKalg, hKfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn
  letI : DivisionRing K := hKdiv
  letI : Algebra k K := hKalg
  letI : Module.Finite k K := hKfin
  letI : FiniteDimensional k K := inferInstance
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) K) := Algebra.IsCentral.of_algEquiv k A _ e
  letI : Algebra.IsCentral k K := isCentral_of_matrix k n K
  refine ⟨K, hKdiv, hKalg, inferInstance, inferInstance, ?_⟩
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  refine ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans e⟩

variable (K K' : Type v) [DivisionRing K] [DivisionRing K']
variable [Algebra k K] [Algebra k K']
variable [Algebra.IsCentral k K] [Algebra.IsCentral k K']
variable [FiniteDimensional k K] [FiniteDimensional k K']

/-- Finite-dimensional central division `k`-algebras determine their Brauer classes uniquely:
matrix algebras over them are Brauer-equivalent iff the division algebras are isomorphic. -/
lemma brauerEquivalent_divisionAlgebra_iff :
    IsBrauerEquivalent
      (CSA.mk (AlgCat.of k K))
      (CSA.mk (AlgCat.of k K')) ↔
      Nonempty (K ≃ₐ[k] K') := by
  constructor
  · rintro ⟨n, m, hn0, hm0, h⟩
    change Nonempty (Matrix (Fin n) (Fin n) K ≃ₐ[k] Matrix (Fin m) (Fin m) K') at h
    rcases h with ⟨e⟩
    letI : NeZero n := ⟨hn0⟩
    letI : NeZero m := ⟨hm0⟩
    let hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    let hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
    letI : IsArtinianRing (Matrix (Fin n) (Fin n) K) :=
      IsArtinianRing.of_finite k (Matrix (Fin n) (Fin n) K)
    letI : Module (Matrix (Fin n) (Fin n) K) (Fin m → K') :=
      Module.compHom (Fin m → K') e.toRingHom
    letI : Module k (Fin m → K') := inferInstance
    letI : IsScalarTower k (Matrix (Fin n) (Fin n) K) (Fin m → K') := by
      refine ⟨?_⟩
      intro c a x
      calc
        e (c • a) • x = (c • e a) • x := by
          congr 1
          simpa [Algebra.smul_def] using
            (show e (((algebraMap k (Matrix (Fin n) (Fin n) K)) c) * a) =
                ((algebraMap k (Matrix (Fin m) (Fin m) K')) c) * e a from
              e.map_mul ((algebraMap k (Matrix (Fin n) (Fin n) K)) c) a)
        _ = c • (e a • x) := smul_assoc c (e a) x
    letI : IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) := IsSimpleModule.matrix_fin_fun hn
    letI : IsSimpleModule (Matrix (Fin m) (Fin m) K') (Fin m → K') := IsSimpleModule.matrix_fin_fun hm
    letI : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
    let compLinearMap : (Fin m → K') →ₛₗ[e.toRingHom] (Fin m → K') :=
      { toFun := id
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    letI : IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin m → K') :=
      (LinearMap.isSimpleModule_iff_of_bijective compLinearMap (Function.bijective_id)).2 inferInstance
    let l : (Fin n → K) ≃ₗ[Matrix (Fin n) (Fin n) K] (Fin m → K') :=
      IsSimpleModule.nonempty_linearEquiv.some
    let eK : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ :=
      matrix_endomorphism_alg_equiv_op hn
    let eComp :
        Module.End (Matrix (Fin n) (Fin n) K) (Fin m → K') ≃ₐ[k]
          Module.End (Matrix (Fin m) (Fin m) K') (Fin m → K') := by
      letI : Module (Matrix (Fin n) (Fin n) K) (Fin m → K') := Module.compHom (Fin m → K') e.toRingHom
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
              map_smul' := by
                intro a x
                exact f.map_smul (e a) x }
          left_inv := by intro f; rfl
          right_inv := by intro f; rfl
          map_mul' := by intro f g; rfl
          map_add' := by intro f g; rfl
          commutes' := by
            intro c
            ext x
            simp [Algebra.algebraMap_eq_smul_one] }
    let eK' : Module.End (Matrix (Fin n) (Fin n) K) (Fin m → K') ≃ₐ[k] K'ᵐᵒᵖ :=
      eComp.trans (matrix_endomorphism_alg_equiv_op hm)
    let hop : Kᵐᵒᵖ ≃ₐ[k] K'ᵐᵒᵖ := eK.symm.trans ((l.conjAlgEquiv k).trans eK')
    exact ⟨AlgEquiv.unop hop⟩
  · rintro ⟨e⟩
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    change Nonempty (Matrix (Fin 1) (Fin 1) K ≃ₐ[k] Matrix (Fin 1) (Fin 1) K')
    exact ⟨(((reindexAlgEquiv k K finOneEquiv).trans uniqueAlgEquiv).trans e).trans
      ((reindexAlgEquiv k K' finOneEquiv).trans uniqueAlgEquiv).symm⟩

end

end
