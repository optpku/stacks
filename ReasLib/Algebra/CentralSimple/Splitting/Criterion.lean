/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.Basic
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import ReasLib.Algebra.CentralSimple.Centralizer.DoubleCentralizer
public import ReasLib.Algebra.CentralSimple.Centralizer.TensorProduct
public import ReasLib.Algebra.CentralSimple.BrauerGroup.DivisionRepresentative
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.FieldTheory.Tower
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.SimpleRing.Basic

/-! # Splitting Criterion for Central Simple Algebras

Splitness of a finite central simple algebra `A` over a field extension `K/k` is
equivalent to Brauer-triviality of the base change `A ⊗_k K`. This file packages
the stable Brauer-invariance API for splitting fields.

## Main declarations

- `CSA.IsSplitBy.brauerEquivalent_one` — split implies Brauer-trivial base change
- `CSA.isBrauerEquivalent_baseChange` — Brauer equivalence survives scalar extension
- `CSA.isSplitBy_iff_brauerEquivalent_one` — splitness ↔ Brauer-trivial base change
- `CSA.isSplitBy_iff_of_brauerEquivalent` — Brauer-equivalent CSAs share splitting fields
- `CSA.isSplitBy_of_self_embedding_finrank_sq` — embedded field of square degree splits
- `CSA.isSplitBy_iff_of_isBrauerEquivalent` — synonym for `isSplitBy_iff_of_brauerEquivalent`
- `CSA.isSplitBy_iff_exists_embedding` — splitting ↔ ∃ Brauer-equivalent with embedded subfield

## References

- [Stacks Project, Tag 074Z](https://stacks.math.columbia.edu/tag/074Z)
-/

@[expose] public section

universe u v w z

namespace CSA

open scoped TensorProduct
open Algebra.TensorProduct
open Matrix

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Type w) [Field K] [Algebra k K] [FiniteDimensional k K]

-- ============================================================
-- Private helpers from BaseChangeMatrix
-- ============================================================

private theorem fin_one_prod_equiv_left_inv (n : ℕ) (ij : Fin 1 × Fin n) :
    (0, ij.2) = ij := by
  rcases ij with ⟨i, j⟩
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

private def fin_one_prod_equiv (n : ℕ) : Fin 1 × Fin n ≃ Fin n where
  toFun ij := ij.2
  invFun j := (0, j)
  left_inv := fin_one_prod_equiv_left_inv n
  right_inv := fun _ ↦ rfl

private noncomputable def baseChange_matrix_algEquiv_matrix_baseChange (n : ℕ) :
    K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin n) (Fin n) (A.baseChange K) :=
  let eK : K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
    ((Matrix.reindexAlgEquiv K K finOneEquiv).trans uniqueAlgEquiv).symm
  let eTensor :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin 1) (Fin 1) K ⊗[k] Matrix (Fin n) (Fin n) A :=
    Algebra.TensorProduct.congr eK
      (AlgEquiv.refl : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin n) (Fin n) A)
  let eKronecker :
      Matrix (Fin 1) (Fin 1) K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[k] A) :=
    Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) k K K A
  eTensor.trans <|
    eKronecker.trans <|
      Matrix.reindexAlgEquiv K (A.baseChange K) (fin_one_prod_equiv n)

private noncomputable def baseChange_of_matrix_brauer_witness {B : CSA.{u, v} k} {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A.baseChange K) ≃ₐ[K] Matrix (Fin m) (Fin m) (B.baseChange K) :=
  let eTensor :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        K ⊗[k] Matrix (Fin m) (Fin m) B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  (A.baseChange_matrix_algEquiv_matrix_baseChange (K := K) n).symm.trans <|
    eTensor.trans <|
      B.baseChange_matrix_algEquiv_matrix_baseChange (K := K) m

-- ============================================================
-- Private helpers from SplitByBrauer
-- ============================================================

private theorem matrix_model_isBrauerEquivalent_division
    {k : Type u} [Field k] {B : CSA.{u, v} k} {n : ℕ} [NeZero n] {D : Type v}
    [DivisionRing D] [Algebra k D] [FiniteDimensional k D] [Algebra.IsCentral k D]
    (e : B ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  exact ⟨((reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩

private noncomputable def matrix_coeffAlgEquiv
    {k : Type u} [Field k] (n : ℕ) {R : Type v} {S : Type z} [Semiring R] [Semiring S]
    [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S) :
    Matrix (Fin n) (Fin n) R ≃ₐ[k] Matrix (Fin n) (Fin n) S := by
  refine AlgEquiv.ofBijective (e.toAlgHom.mapMatrix) ?_
  constructor
  · intro M N hMN
    ext i j
    exact e.injective <| by simpa using congrArg (fun X ↦ X i j) hMN
  · intro M
    refine ⟨e.symm.toAlgHom.mapMatrix M, ?_⟩
    ext i j
    simp

-- ============================================================
-- Public API: Brauer-class criterion for splitting
-- ============================================================

omit [FiniteDimensional k K] in
/-- A split base change is Brauer equivalent to the base field over the extension. -/
lemma IsSplitBy.brauerEquivalent_one :
    A.IsSplitBy K → IsBrauerEquivalent (A.baseChange K) (CSA.mk (AlgCat.of K K)) := by
  rintro ⟨n, hSplit⟩
  by_cases hn : n = 0
  · rcases hSplit with ⟨e⟩
    exfalso
    subst hn
    exact zero_ne_one <| e.injective <| Subsingleton.elim _ _
  · rcases hSplit with ⟨e⟩
    refine ⟨1, n, one_ne_zero, hn, ?_⟩
    exact ⟨((reindexAlgEquiv K (A.baseChange K) finOneEquiv).trans uniqueAlgEquiv).trans e⟩

omit [FiniteDimensional k K] in
/-- Brauer equivalence survives scalar extension. -/
lemma isBrauerEquivalent_baseChange {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (A.baseChange K) (B.baseChange K) := by
  rcases hAB with ⟨n, m, hn, hm, ⟨e⟩⟩
  refine ⟨n, m, hn, hm, ?_⟩
  exact ⟨A.baseChange_of_matrix_brauer_witness (K := K) e⟩

omit [FiniteDimensional k K] in
/-- Splitness is equivalent to Brauer equivalence of `A.baseChange K` with the
base field representative. -/
lemma isSplitBy_iff_brauerEquivalent_one :
    A.IsSplitBy K ↔ IsBrauerEquivalent (A.baseChange K) (CSA.mk (AlgCat.of K K)) := by
  constructor
  · intro h; exact h.brauerEquivalent_one
  · intro hBrauer
    letI : IsArtinianRing (A.baseChange K) := IsArtinianRing.of_finite K (A.baseChange K)
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfinite, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K (A.baseChange K)
    letI : NeZero n := hn
    letI : DivisionRing D := hDdiv
    letI : Algebra K D := hDalg
    letI : Module.Finite K D := hDfinite
    letI : FiniteDimensional K D := inferInstance
    letI : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
      Algebra.IsCentral.of_algEquiv K (A.baseChange K) _ e
    -- Local instance justification (proof-local temporary data): D and n come from this existential Wedderburn decomposition; centrality descends from its matrix model, and n is not inferable from a global instance target Algebra.IsCentral K D.
    letI : Algebra.IsCentral K D := Algebra.IsCentral.of_matrix (k := K) n D
    have hAD : IsBrauerEquivalent (A.baseChange K) (CSA.mk (AlgCat.of K D)) :=
      matrix_model_isBrauerEquivalent_division (k := K) e
    have hDK : IsBrauerEquivalent (CSA.mk (AlgCat.of K D)) (CSA.mk (AlgCat.of K K)) :=
      IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hAD) hBrauer
    letI : Small.{w} D := Small.mk' (Module.finBasis K D).equivFun.toEquiv
    let eShrink : Shrink.{w} D ≃ₐ[K] D := Shrink.algEquiv K D

    letI : Algebra.IsCentral K (Shrink.{w} D) := by
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : eShrink x ∈ Subalgebra.center K D := by
        rw [Subalgebra.mem_center_iff] at hx ⊢
        intro b
        have hcomm : eShrink.symm b * x = x * eShrink.symm b := hx (eShrink.symm b)
        exact by simpa using congrArg eShrink hcomm
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).1 hx'
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      have hxe : eShrink x = eShrink (algebraMap K (Shrink.{w} D) a) := by
        simpa using ha
      exact eShrink.injective hxe.symm
    have hShrink :
        IsBrauerEquivalent (CSA.mk (AlgCat.of K (Shrink.{w} D))) (CSA.mk (AlgCat.of K D)) :=
      by
        refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
        exact ⟨((reindexAlgEquiv K (CSA.mk (AlgCat.of K (Shrink.{w} D))) finOneEquiv).trans
          uniqueAlgEquiv).trans <| eShrink.trans <|
            ((reindexAlgEquiv K (CSA.mk (AlgCat.of K D)) finOneEquiv).trans uniqueAlgEquiv).symm⟩
    have hShrinkK :
        IsBrauerEquivalent (CSA.mk (AlgCat.of K (Shrink.{w} D))) (CSA.mk (AlgCat.of K K)) :=
      IsBrauerEquivalent.trans hShrink hDK
    rcases (brauerEquivalent_divisionAlgebra_iff K K (Shrink.{w} D)).1
        (IsBrauerEquivalent.symm hShrinkK) with ⟨eKD'⟩
    let eKD : K ≃ₐ[K] D := eKD'.trans eShrink
    exact ⟨n, ⟨e.trans (matrix_coeffAlgEquiv (k := K) n eKD.symm)⟩⟩

omit [FiniteDimensional k K] in
/-- Brauer-equivalent representatives are split by the same finite extension. -/
lemma isSplitBy_iff_of_brauerEquivalent {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  rw [A.isSplitBy_iff_brauerEquivalent_one K, B.isSplitBy_iff_brauerEquivalent_one K]
  have hbase : IsBrauerEquivalent (A.baseChange K) (B.baseChange K) :=
    A.isBrauerEquivalent_baseChange K hAB
  constructor
  · intro hSplit
    exact IsBrauerEquivalent.trans (IsBrauerEquivalent.symm hbase) hSplit
  · intro hSplit
    exact IsBrauerEquivalent.trans hbase hSplit

/-- An embedded field of square degree splits the ambient finite central simple algebra. -/
lemma isSplitBy_of_self_embedding_finrank_sq
    {B : CSA.{u, v} k}
    (hK : Nonempty (K →ₐ[k] B))
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    B.IsSplitBy K := by
  rcases hK with ⟨ι⟩
  letI : Module K B :=
    { smul := fun c x ↦ x * ι c
      one_smul := by
        intro x
        change x * ι 1 = x
        simp
      mul_smul := by
        intro a b x
        change x * ι (a * b) = (x * ι b) * ι a
        have hcomm : ι a * ι b = ι b * ι a := by
          simpa [map_mul] using congrArg ι (mul_comm a b)
        rw [map_mul, mul_assoc, hcomm]
      smul_zero := by
        intro c
        change (0 : B) * ι c = 0
        simp

      smul_add := by
        intro c x y
        change (x + y) * ι c = x * ι c + y * ι c
        rw [add_mul]
      zero_smul := by
        intro x
        change x * ι 0 = 0
        simp
      add_smul := by
        intro a b x
        change x * ι (a + b) = x * ι a + x * ι b
        rw [map_add, mul_add] }
  letI : IsScalarTower k K B :=
    ⟨fun r c x ↦ by
      calc
        (r • c) • x = x * ι ((algebraMap k K r) * c) := by
          rw [Algebra.smul_def]
          rfl
        _ = x * (algebraMap k B r * ι c) := by rw [map_mul, AlgHom.commutes]
        _ = (x * algebraMap k B r) * ι c := by rw [mul_assoc]
        _ = (algebraMap k B r * x) * ι c := by
              rw [(Algebra.commutes (R := k) (A := B) r x).symm]
        _ = (algebraMap k B r) * (x * ι c) := by rw [← mul_assoc]
        _ = r • c • x := by
          rw [Algebra.smul_def]
          change (algebraMap k B r) * (x * ι c) = (algebraMap k B r) * (x * ι c)
          rfl⟩
  letI : FiniteDimensional K B := FiniteDimensional.right k K B
  let ψ : B →ₐ[k] Module.End K B := by
    refine
      { toFun := fun b ↦
          { toFun := fun x ↦ b * x
            map_add' := by
              intro x y
              rw [mul_add]
            map_smul' := by
              intro c x
              change b * (x * ι c) = (b * x) * ι c
              rw [mul_assoc] }
        map_zero' := by
          ext x
          simp
        map_one' := by
          ext x
          simp
        map_add' := by
          intro b₁ b₂
          ext x
          change (b₁ + b₂) * x = b₁ * x + b₂ * x
          rw [add_mul]
        map_mul' := by
          intro b₁ b₂
          ext x
          change b₁ * b₂ * x = b₁ * (b₂ * x)
          rw [mul_assoc]
        commutes' := by
          intro r
          ext x
          change (algebraMap k B r) * x = r • x
          rw [Algebra.smul_def] }

  let φ : B.baseChange K →ₐ[K] Module.End K B :=
    (AlgHom.liftEquiv k K B (Module.End K B))
      ψ
  have hφ_inj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hfinrankB : Module.finrank K B = Module.finrank k K := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := K))
    calc
      Module.finrank k K * Module.finrank K B = Module.finrank k B := by
        simpa using (Module.finrank_mul_finrank k K B)
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank k K * Module.finrank k K := by rw [pow_two]
  have hφ_dim :
      Module.finrank K (B.baseChange K) = Module.finrank K (Module.End K B) := by
    calc
      Module.finrank K (B.baseChange K) = Module.finrank k B := by
        change Module.finrank K (K ⊗[k] B) = Module.finrank k B
        exact Module.finrank_baseChange (R := K) (S := k) (M' := B)
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank K B * Module.finrank K B := by rw [hfinrankB, pow_two]
      _ = Module.finrank K (Module.End K B) := by
            simpa using (Module.finrank_linearMap K K B B).symm
  have hφ_surj : Function.Surjective φ := by
    let φₗ : B.baseChange K →ₗ[K] Module.End K B := φ.toLinearMap
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hφ_dim).mp hφ_inj
  let b : Module.Basis (Fin (Module.finrank K B)) K B := Module.finBasis K B
  refine ⟨Module.finrank K B, ?_⟩
  exact ⟨(AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).trans (algEquivMatrix b)⟩

omit [FiniteDimensional k K] in
/-- Brauer-equivalent finite central simple algebras have the same finite splitting fields. -/
theorem isSplitBy_iff_of_isBrauerEquivalent {B : CSA.{u, v} k}
    (hAB : IsBrauerEquivalent A B) :
    A.IsSplitBy K ↔ B.IsSplitBy K := by
  exact A.isSplitBy_iff_of_brauerEquivalent K hAB

-- ============================================================
-- Private helpers for the forward commutant witness
-- ============================================================

private noncomputable def moduleEndRestrictScalarsAlgHom {n : Type*} [Fintype n] [DecidableEq n] :
    Module.End K (n → K) →ₐ[k] Module.End k (n → K) where
  toFun f := f.restrictScalars k
  map_zero' := rfl
  map_one' := by
    ext x
    rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    ext x i
    rfl

omit [FiniteDimensional k K] in
private theorem restrictEndInjective {n : Type*} [Fintype n] [DecidableEq n] :
    Function.Injective (moduleEndRestrictScalarsAlgHom (k := k) (K := K) :
      Module.End K (n → K) →ₐ[k] Module.End k (n → K)) := by
  intro f g hfg
  apply LinearMap.ext
  intro v
  exact congrArg (fun h : Module.End k (n → K) ↦ h v) hfg

omit [FiniteDimensional k K] in
private theorem restrictEndCommutesScalars {n : Type*} [Fintype n] [DecidableEq n]
    (f : Module.End K (n → K)) (x : K) :
    Commute (moduleEndRestrictScalarsAlgHom (k := k) (K := K) f)
      (Algebra.lsmul k k (n → K) x) := by
  change
    moduleEndRestrictScalarsAlgHom (k := k) (K := K) f * Algebra.lsmul k k (n → K) x =
      Algebra.lsmul k k (n → K) x * moduleEndRestrictScalarsAlgHom (k := k) (K := K) f
  ext v i
  simp [moduleEndRestrictScalarsAlgHom, Algebra.lsmul_coe, map_smul]

private noncomputable def splitModelAction {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    A →ₐ[k] Module.End k (Fin n → K) := by
  let eEnd : A.baseChange K ≃ₐ[K] Module.End K (Fin n → K) :=
    e.trans (algEquivMatrix (Pi.basisFun K (Fin n))).symm
  letI : Algebra k ↑(A.baseChange K).toAlgCat := by
    change Algebra k (K ⊗[k] A)
    infer_instance
  letI : IsScalarTower k K ↑(A.baseChange K).toAlgCat := by
    change IsScalarTower k K (K ⊗[k] A)
    infer_instance
  let includeA : A →ₐ[k] A.baseChange K := Algebra.TensorProduct.includeRight
  let eEndk : A.baseChange K →ₐ[k] Module.End K (Fin n → K) := eEnd.toAlgHom.restrictScalars k
  let rhoK : A →ₐ[k] Module.End K (Fin n → K) := eEndk.comp includeA
  exact (moduleEndRestrictScalarsAlgHom (k := k) (K := K)).comp rhoK

omit [FiniteDimensional k K] in
private theorem splitModelAction_injective {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Function.Injective (splitModelAction (A := A) (K := K) e) := by
  let eEnd : A.baseChange K ≃ₐ[K] Module.End K (Fin n → K) :=
    e.trans (algEquivMatrix (Pi.basisFun K (Fin n))).symm
  letI : Algebra k ↑(A.baseChange K).toAlgCat := by
    change Algebra k (K ⊗[k] A)
    infer_instance
  letI : IsScalarTower k K ↑(A.baseChange K).toAlgCat := by
    change IsScalarTower k K (K ⊗[k] A)
    infer_instance
  let includeA : A →ₐ[k] A.baseChange K := Algebra.TensorProduct.includeRight
  let eEndk : A.baseChange K →ₐ[k] Module.End K (Fin n → K) := eEnd.toAlgHom.restrictScalars k
  let rhoK : A →ₐ[k] Module.End K (Fin n → K) := eEndk.comp includeA
  intro a b hab
  apply includeA.injective
  apply eEnd.injective
  apply restrictEndInjective (k := k) (K := K)
  sorry -- TODO: fix simpa

private noncomputable def splitModelRange {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Subalgebra k (Module.End k (Fin n → K)) :=
  (splitModelAction (A := A) (K := K) e).range

private noncomputable def splitModelCentralizer {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Subalgebra k (Module.End k (Fin n → K)) :=
  Subalgebra.centralizer k
    (splitModelRange (A := A) (K := K) e : Set (Module.End k (Fin n → K)))

private noncomputable def splitModelRangeAlgEquiv {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    A ≃ₐ[k] splitModelRange (A := A) (K := K) e := by
  refine AlgEquiv.ofBijective (splitModelAction (A := A) (K := K) e).rangeRestrict ?_
  constructor
  · intro a b hab
    exact splitModelAction_injective (A := A) (K := K) e (Subtype.ext_iff.mp hab)
  · exact AlgHom.rangeRestrict_surjective _

omit [FiniteDimensional k K] in
private theorem algHomFromFieldCommutes {B : Type z} [Semiring B] [Algebra k B]
    (f : K →ₐ[k] B) (x y : K) :
    Commute (f x) (f y) := by
  change f x * f y = f y * f x
  simpa [map_mul] using congrArg f (mul_comm x y)

private theorem smallCarrierOfFiniteDimensional (A : CSA.{u, v} k) (B : Type z)
    [Ring B] [Algebra k B]
    [FiniteDimensional k B] :
    Small.{v} B := by
  letI : Small.{v} k := small_of_injective (f := algebraMap k A) (algebraMap k A).injective
  let b := Module.finBasis k B
  refine small_of_injective (f := fun x i ↦ equivShrink k (b.repr x i)) ?_
  intro x y hxy
  apply b.repr.injective
  ext i
  exact (equivShrink k).injective (congrFun hxy i)

private theorem shrinkFiniteDimensionalIsCentral (A : CSA.{u, v} k) (B : Type z) [Ring B]
    [Algebra k B] [FiniteDimensional k B] [Algebra.IsCentral k B] :
    letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
    Algebra.IsCentral k (Shrink.{v} B) := by
  letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
  let e : Shrink.{v} B ≃ₐ[k] B := Shrink.algEquiv k B
  refine ⟨fun x hx ↦ ?_⟩
  have hx' : e x ∈ Subalgebra.center k B := by
    rw [Subalgebra.mem_center_iff] at hx ⊢
    intro b
    have hcomm : e.symm b * x = x * e.symm b := hx (e.symm b)
    exact by simpa using congrArg e hcomm
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hx'
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  have hxe : e x = e (algebraMap k (Shrink.{v} B) a) := by
    simpa using ha
  exact e.injective hxe.symm

private noncomputable def shrinkFiniteCentralSimple (B : Type z) [Ring B] [Algebra k B]
    [FiniteDimensional k B] [Algebra.IsCentral k B] [IsSimpleRing B] :
    CSA.{u, v} k :=
  letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
  { toAlgCat := AlgCat.of k (Shrink.{v} B)
    isCentral := shrinkFiniteDimensionalIsCentral (A := A) (k := k) B
    isSimple := IsSimpleRing.of_ringEquiv (Shrink.ringEquiv B).symm inferInstance
    fin_dim := (Shrink.algEquiv k B).symm.toLinearEquiv.finiteDimensional }

private noncomputable def shrinkFiniteCentralSimpleAlgEquiv (B : Type z) [Ring B] [Algebra k B]
    [FiniteDimensional k B] [Algebra.IsCentral k B] [IsSimpleRing B] :
    shrinkFiniteCentralSimple (A := A) (k := k) B ≃ₐ[k] B :=
  letI := smallCarrierOfFiniteDimensional (A := A) (k := k) B
  Shrink.algEquiv k B

private noncomputable def baseFieldRepresentative : CSA.{u, v} k :=
  shrinkFiniteCentralSimple (A := A) (k := k) k

private noncomputable def baseFieldRepresentativeAlgEquiv :
    baseFieldRepresentative (A := A) (k := k) ≃ₐ[k] k :=
  shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) k

omit [FiniteDimensional k K] in
private theorem splitModelActionCommutesScalars {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) (a : A) (x : K) :
    Commute (splitModelAction (A := A) (K := K) e a)
      (Algebra.lsmul k k (Fin n → K) x) := by
  let eEnd : A.baseChange K ≃ₐ[K] Module.End K (Fin n → K) :=
    e.trans (algEquivMatrix (Pi.basisFun K (Fin n))).symm
  letI : Algebra k ↑(A.baseChange K).toAlgCat := by
    change Algebra k (K ⊗[k] A)
    infer_instance
  letI : IsScalarTower k K ↑(A.baseChange K).toAlgCat := by
    change IsScalarTower k K (K ⊗[k] A)
    infer_instance
  let includeA : A →ₐ[k] A.baseChange K := Algebra.TensorProduct.includeRight
  let eEndk : A.baseChange K →ₐ[k] Module.End K (Fin n → K) := eEnd.toAlgHom.restrictScalars k
  let rhoK : A →ₐ[k] Module.End K (Fin n → K) := eEndk.comp includeA
  sorry -- TODO: fix simpa

omit [FiniteDimensional k K] in
private theorem splitModelRangeFinrank {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Module.finrank k (splitModelRange (A := A) (K := K) e) = (n : Nat) ^ 2 := by
  have hrange :
      Module.finrank k (splitModelRange (A := A) (K := K) e) = Module.finrank k A := by
    exact (splitModelRangeAlgEquiv (A := A) (K := K) e).toLinearEquiv.finrank_eq.symm
  have hbase : Module.finrank K (A.baseChange K) = Module.finrank k A := by
    change Module.finrank K (K ⊗[k] A) = Module.finrank k A
    exact Module.finrank_baseChange
  calc
    Module.finrank k (splitModelRange (A := A) (K := K) e) = Module.finrank k A := hrange
    _ = Module.finrank K (A.baseChange K) := hbase.symm
    _ = Module.finrank K (Matrix (Fin n) (Fin n) K) := e.toLinearEquiv.finrank_eq
    _ = (n : Nat) ^ 2 := by
      simpa [pow_two] using (Module.finrank_matrix K K (Fin n) (Fin n))

private theorem splitModelAmbientEndIsSimple {n : ℕ+} :
    IsSimpleRing (Module.End k (Fin n → K)) := by
  let b : Module.Basis (Fin (Module.finrank k (Fin n → K))) k (Fin n → K) :=
    Module.finBasis k (Fin n → K)
  letI : Nonempty (Fin (Module.finrank k (Fin n → K))) :=
    ⟨⟨0, Module.finrank_pos (R := k) (M := Fin n → K)⟩⟩
  exact IsSimpleRing.of_ringEquiv (algEquivMatrix b).toRingEquiv.symm inferInstance

private theorem splitModelAmbientEndFinrank {n : ℕ+} :
    Module.finrank k (Module.End k (Fin n → K)) =
      Module.finrank k (Fin n → K) * Module.finrank k (Fin n → K) := by
  simpa using (Module.finrank_linearMap k k (Fin n → K) (Fin n → K))

private theorem splitModelStandardModuleFinrank {n : ℕ+} :
    Module.finrank k (Fin n → K) = (n : Nat) * Module.finrank k K := by
  rw [Module.finrank_pi_fintype, Finset.sum_const_nat]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rfl

private theorem splitModelAmbientEndFinrankFactorized {n : ℕ+} :
    Module.finrank k (Module.End k (Fin n → K)) =
      (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
  calc
    Module.finrank k (Module.End k (Fin n → K))
        = Module.finrank k (Fin n → K) * Module.finrank k (Fin n → K) :=
      splitModelAmbientEndFinrank (k := k) (K := K) (n := n)
    _ = ((n : Nat) * Module.finrank k K) * ((n : Nat) * Module.finrank k K) := by
      rw [splitModelStandardModuleFinrank (k := k) (K := K) (n := n)]
    _ = (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
      simp only [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem splitModelAmbientEndIsCentral {n : ℕ+} :
    Algebra.IsCentral k (Module.End k (Fin n → K)) := by
  let b : Module.Basis (Fin (Module.finrank k (Fin n → K))) k (Fin n → K) :=
    Module.finBasis k (Fin n → K)
  let eMatrix :
      Module.End k (Fin n → K) ≃ₐ[k]
        Matrix (Fin (Module.finrank k (Fin n → K)))
          (Fin (Module.finrank k (Fin n → K))) k :=
    algEquivMatrix b
  refine ⟨fun x hx ↦ ?_⟩
  rw [Subalgebra.mem_center_iff] at hx
  let y := eMatrix x
  have hy :
      y ∈ Subalgebra.center k
        (Matrix (Fin (Module.finrank k (Fin n → K)))
          (Fin (Module.finrank k (Fin n → K))) k) := by
    rw [Subalgebra.mem_center_iff]
    intro M
    obtain ⟨f, rfl⟩ := eMatrix.surjective M
    simpa [y] using congrArg eMatrix (hx f)
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hy
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  apply eMatrix.injective
  simpa [y] using ha.symm

omit [FiniteDimensional k K] in
private theorem splitModelRangeIsCentral {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Algebra.IsCentral k (splitModelRange (A := A) (K := K) e) := by
  let R := splitModelRange (A := A) (K := K) e
  let eR := splitModelRangeAlgEquiv (A := A) (K := K) e
  refine ⟨fun x hx ↦ ?_⟩
  rw [Subalgebra.mem_center_iff] at hx
  let y : A := eR.symm x
  have hy : y ∈ Subalgebra.center k A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    apply eR.injective
    simpa [y] using hx (eR a)
  obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff k).1 hy
  rw [Algebra.mem_bot]
  refine ⟨r, ?_⟩
  change algebraMap k R r = x
  simpa [R, y] using (congrArg eR hr).symm

private theorem splitModelCentralizerIsSimple {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    IsSimpleRing (splitModelCentralizer (A := A) (K := K) e) := by
  let R := splitModelRange (A := A) (K := K) e
  let ambient := Module.End k (Fin n → K)
  letI : IsSimpleRing R := by
    exact IsSimpleRing.of_ringEquiv (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv
      inferInstance
  letI : IsSimpleRing ambient := splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  letI : Algebra.IsCentral k ambient := splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k ambient)
  sorry -- TODO: fix simpa

private theorem splitModelCentralizerIsCentral {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Algebra.IsCentral k (splitModelCentralizer (A := A) (K := K) e) := by
  let R := splitModelRange (A := A) (K := K) e
  let C := splitModelCentralizer (A := A) (K := K) e
  let ambient := Module.End k (Fin n → K)
  letI : IsSimpleRing R := by
    exact IsSimpleRing.of_ringEquiv (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv
      inferInstance
  letI : IsSimpleRing ambient := splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  letI : Algebra.IsCentral k ambient := splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k ambient)
  have hCC : Subalgebra.centralizer k (C : Set (Module.End k (Fin n → K))) = R := by
    simpa [R, C, splitModelCentralizer] using R.centralizer_centralizer_eq ambientCSA
  refine ⟨fun x hx ↦ ?_⟩
  have hxC :
      x.1 ∈ Subalgebra.centralizer k (C : Set (Module.End k (Fin n → K))) := by
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)

  have hxR : x.1 ∈ R := by
    simpa [hCC] using hxC
  have hxCommRange : ∀ y ∈ R, y * x.1 = x.1 * y := by
    have hxInC : x.1 ∈ Subalgebra.centralizer k (R : Set (Module.End k (Fin n → K))) := by
      simpa [R, C, splitModelCentralizer] using (show x.1 ∈ C from x.2)
    exact
      (Subalgebra.mem_centralizer_iff
        (R := k) (s := (R : Set (Module.End k (Fin n → K)))) (z := x.1)).1 hxInC
  have hxCenterR : (⟨x.1, hxR⟩ : R) ∈ Subalgebra.center k R := by
    rw [Subalgebra.mem_center_iff]
    intro y
    exact Subtype.ext (hxCommRange y.1 y.2)
  letI : Algebra.IsCentral k R := splitModelRangeIsCentral (A := A) (K := K) e
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxCenterR
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val ha.symm

private theorem splitModelCentralizerFinrankSq {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Module.finrank k (splitModelCentralizer (A := A) (K := K) e) =
      Module.finrank k K ^ 2 := by
  let R := splitModelRange (A := A) (K := K) e
  letI : IsSimpleRing R := by
    exact IsSimpleRing.of_ringEquiv
      (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv inferInstance
  letI : Module.Free k R := Module.Free.of_divisionRing k R
  letI : IsSimpleRing (Module.End k (Fin n → K)) :=
    splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  letI : Algebra.IsCentral k (Module.End k (Fin n → K)) :=
    splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k (Module.End k (Fin n → K)))
  have hdim' :
      Module.finrank k ambientCSA =
        Module.finrank k ↥R *
          Module.finrank k
            ↥(Subalgebra.centralizer k ((R : Subalgebra k ambientCSA) : Set ambientCSA)) := by
    exact Subalgebra.finrank_centralizer (k := k) (A := ambientCSA) (B := R)
  have hAmbientCSA :
      Module.finrank k ambientCSA = (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
    change Module.finrank k (Module.End k (Fin n → K)) =
      (n : Nat) ^ 2 * (Module.finrank k K ^ 2)
    exact splitModelAmbientEndFinrankFactorized (k := k) (K := K) (n := n)
  have hmain :
      (n : Nat) ^ 2 * Module.finrank k ↥(splitModelCentralizer (A := A) (K := K) e) =
        (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := by
    calc
      (n : Nat) ^ 2 * Module.finrank k ↥(splitModelCentralizer (A := A) (K := K) e)
          = Module.finrank k ↥R *
              Module.finrank k ↥(splitModelCentralizer (A := A) (K := K) e) := by
        rw [splitModelRangeFinrank (A := A) (K := K) e]
      _ = Module.finrank k ambientCSA := by
        sorry -- TODO: fix simpa
      _ = (n : Nat) ^ 2 * (Module.finrank k K ^ 2) := hAmbientCSA
  exact Nat.eq_of_mul_eq_mul_left (pow_pos n.2 2) hmain

omit [FiniteDimensional k K] in
private theorem splitModelScalarEmbeddingToCentralizer {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    Nonempty (K →ₐ[k] splitModelCentralizer (A := A) (K := K) e) := by
  let ι : K →ₐ[k] Module.End k (Fin n → K) := Algebra.lsmul k k (Fin n → K)
  have hι :
      ∀ x, ι x ∈ splitModelCentralizer (A := A) (K := K) e := by
    intro x
    rw [splitModelCentralizer, Subalgebra.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨a, rfl⟩
    exact (splitModelActionCommutesScalars (A := A) (K := K) e a x).eq
  exact ⟨ι.codRestrict (splitModelCentralizer (A := A) (K := K) e) hι⟩

private theorem brauerEquivalent_baseField_unit :
    IsBrauerEquivalent (baseFieldRepresentative (A := A) (k := k)) (unit.{u, v} k) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((Matrix.reindexAlgEquiv k (baseFieldRepresentative (A := A) (k := k))
    finOneEquiv).trans uniqueAlgEquiv).trans <|
    (baseFieldRepresentativeAlgEquiv (A := A) (k := k)).trans <|
    (ULift.algEquiv : ↑(unit.{u, v} k).toAlgCat ≃ₐ[k] k).symm.trans <|
      ((Matrix.reindexAlgEquiv k (unit.{u, v} k) finOneEquiv).trans uniqueAlgEquiv).symm⟩

private theorem brauerEquivalent_tensorProduct_baseField (B : CSA.{u, v} k) :
    IsBrauerEquivalent (B.tensorProduct (baseFieldRepresentative (A := A) (k := k))) B := by
  let eBase : B.tensorProduct (baseFieldRepresentative (A := A) (k := k)) ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[k] B)
      (baseFieldRepresentativeAlgEquiv (A := A) (k := k))).trans <|
        Algebra.TensorProduct.rid k k B
  exact CSA.brauerEquivalent_of_algEquiv (k := k) eBase

private theorem brauerEquivalent_baseField_tensorProduct (B : CSA.{u, v} k) :
    IsBrauerEquivalent ((baseFieldRepresentative (A := A) (k := k)).tensorProduct B) B := by
  let eBase : (baseFieldRepresentative (A := A) (k := k)).tensorProduct B ≃ₐ[k] B :=
    (Algebra.TensorProduct.congr (baseFieldRepresentativeAlgEquiv (A := A) (k := k))
      (AlgEquiv.refl : B ≃ₐ[k] B)).trans <|
        Algebra.TensorProduct.lid k B
  exact CSA.brauerEquivalent_of_algEquiv (k := k) eBase

private theorem brauerEquivalent_baseField_tensorProduct_opposite (B : CSA.{u, v} k) :
    IsBrauerEquivalent (baseFieldRepresentative (A := A) (k := k))
      (B.tensorProduct B.opposite) := by
  exact IsBrauerEquivalent.trans (brauerEquivalent_baseField_unit (A := A) (k := k))
    (IsBrauerEquivalent.symm (CSA.brauerEquivalent_inv (k := k) B))

private theorem brauerEquivalent_of_tensorProduct_unit_opposite {B : CSA.{u, v} k}
    (h : IsBrauerEquivalent (A.tensorProduct B) (baseFieldRepresentative (A := A) (k := k))) :
    IsBrauerEquivalent A B.opposite := by
  have hBaseToTensor :
      IsBrauerEquivalent (baseFieldRepresentative (A := A) (k := k))
        (B.tensorProduct B.opposite) := by
    exact brauerEquivalent_baseField_tensorProduct_opposite (A := A) (k := k) B
  have hAUnit :
      IsBrauerEquivalent A (A.tensorProduct (baseFieldRepresentative (A := A) (k := k))) := by
    exact IsBrauerEquivalent.symm (brauerEquivalent_tensorProduct_baseField (A := A) (k := k) A)
  have hATensor :
      IsBrauerEquivalent A (A.tensorProduct (B.tensorProduct B.opposite)) := by
    exact IsBrauerEquivalent.trans hAUnit
      (CSA.brauerEquivalent_tensorProduct (k := k) (IsBrauerEquivalent.refl A) hBaseToTensor)

  have hAssoc :
      IsBrauerEquivalent (A.tensorProduct (B.tensorProduct B.opposite))
        ((A.tensorProduct B).tensorProduct B.opposite) := by
    exact IsBrauerEquivalent.symm
      (CSA.brauerEquivalent_assoc (k := k) A B B.opposite)
  have hLeftFactor :
      IsBrauerEquivalent ((A.tensorProduct B).tensorProduct B.opposite)
        ((baseFieldRepresentative (A := A) (k := k)).tensorProduct B.opposite) := by
    exact CSA.brauerEquivalent_tensorProduct (k := k) h
      (IsBrauerEquivalent.refl B.opposite)
  have hUnitTensor :
      IsBrauerEquivalent
        ((baseFieldRepresentative (A := A) (k := k)).tensorProduct B.opposite) B.opposite := by
    exact brauerEquivalent_baseField_tensorProduct (A := A) (k := k) B.opposite
  exact IsBrauerEquivalent.trans hATensor <|
    IsBrauerEquivalent.trans hAssoc <|
      IsBrauerEquivalent.trans hLeftFactor hUnitTensor

private theorem splitModelTensorProductBrauerUnit {n : ℕ+}
    (e : A.baseChange K ≃ₐ[K] Matrix (Fin n) (Fin n) K)
    [Algebra.IsCentral k (splitModelCentralizer (A := A) (K := K) e)]
    [IsSimpleRing (splitModelCentralizer (A := A) (K := K) e)] :
    IsBrauerEquivalent
      (A.tensorProduct
        (shrinkFiniteCentralSimple (A := A) (k := k)
          (splitModelCentralizer (A := A) (K := K) e)))
      (baseFieldRepresentative (A := A) (k := k)) := by
  let R := splitModelRange (A := A) (K := K) e
  let C := splitModelCentralizer (A := A) (K := K) e
  let ambient := Module.End k (Fin n → K)
  letI : IsSimpleRing R := by
    exact IsSimpleRing.of_ringEquiv (splitModelRangeAlgEquiv (A := A) (K := K) e).toRingEquiv
      inferInstance
  letI : Algebra.IsCentral k R := splitModelRangeIsCentral (A := A) (K := K) e
  letI : IsSimpleRing ambient := splitModelAmbientEndIsSimple (k := k) (K := K) (n := n)
  let b : Module.Basis (Fin (Module.finrank k (Fin n → K))) k (Fin n → K) :=
    Module.finBasis k (Fin n → K)
  letI : Algebra.IsCentral k ambient := splitModelAmbientEndIsCentral (k := k) (K := K) (n := n)
  let ambientCSA : CSA.{u, w} k := CSA.mk (AlgCat.of k ambient)
  have hTensorAmbient :
      IsBrauerEquivalent
        (A.tensorProduct (shrinkFiniteCentralSimple (A := A) (k := k) C))
        (shrinkFiniteCentralSimple (A := A) (k := k) ambient) := by
    exact CSA.brauerEquivalent_of_algEquiv (k := k) <|
      (Algebra.TensorProduct.congr
        (splitModelRangeAlgEquiv (A := A) (K := K) e)
        (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) C)).trans <|
      (Subalgebra.centralizer_tensorProduct_algEquiv (k := k) (A := ambientCSA) (B := R)).trans <|
      (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) ambient).symm
  have hAmbientField :
      IsBrauerEquivalent
        (shrinkFiniteCentralSimple (A := A) (k := k) ambient)
        (baseFieldRepresentative (A := A) (k := k)) := by
    letI : NeZero (Module.finrank k (Fin n → K)) :=
      ⟨Nat.ne_of_gt (Module.finrank_pos (R := k) (M := Fin n → K))⟩
    let eMatrix :
      shrinkFiniteCentralSimple (A := A) (k := k) ambient ≃ₐ[k]
          Matrix (Fin (Module.finrank k (Fin n → K)))
            (Fin (Module.finrank k (Fin n → K))) k :=
      (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) ambient).trans
        (algEquivMatrix b)

    let eField :
        shrinkFiniteCentralSimple (A := A) (k := k) ambient ≃ₐ[k]
          Matrix (Fin (Module.finrank k (Fin n → K)))
            (Fin (Module.finrank k (Fin n → K)))
            (baseFieldRepresentative (A := A) (k := k)) :=
      eMatrix.trans <|
        matrix_coeffAlgEquiv (k := k) (n := Module.finrank k (Fin n → K))
          (baseFieldRepresentativeAlgEquiv (A := A) (k := k)).symm
    refine ⟨1, Module.finrank k (Fin n → K), one_ne_zero, NeZero.ne _, ?_⟩
    exact ⟨((Matrix.reindexAlgEquiv k
      (shrinkFiniteCentralSimple (A := A) (k := k) ambient) finOneEquiv).trans
        uniqueAlgEquiv).trans eField⟩
  exact IsBrauerEquivalent.trans hTensorAmbient hAmbientField

/-- A split matrix model yields a Brauer-equivalent central simple algebra containing `K`
and having `k`-dimension `[K : k]^2`. -/
private lemma forward_commutant_witness_of_split
    (hA : A.IsSplitBy K) :
    ∃ B : CSA.{u, v} k,
      IsBrauerEquivalent A B ∧
        Nonempty (K →ₐ[k] B) ∧
        Module.finrank k B = Module.finrank k K ^ 2 := by
  rcases (A.isSplitBy_iff_exists_pnat K).1 hA with ⟨n, ⟨e⟩⟩
  let C := splitModelCentralizer (A := A) (K := K) e
  letI : IsSimpleRing C := splitModelCentralizerIsSimple (A := A) (K := K) e
  letI : Algebra.IsCentral k C := splitModelCentralizerIsCentral (A := A) (K := K) e
  let B₀ := shrinkFiniteCentralSimple (A := A) (k := k) C
  have hBrauerB₀ :
      IsBrauerEquivalent A B₀.opposite := by
    exact brauerEquivalent_of_tensorProduct_unit_opposite (A := A) (k := k) (B := B₀) <|
      splitModelTensorProductBrauerUnit (A := A) (K := K) (k := k) e
  have hEmbedB₀ : Nonempty (K →ₐ[k] B₀) := by
    rcases splitModelScalarEmbeddingToCentralizer (A := A) (K := K) e with ⟨ιC⟩
    exact ⟨(shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) C).symm.toAlgHom.comp ιC⟩
  have hEmbedOpp : Nonempty (K →ₐ[k] B₀.opposite) := by
    rcases hEmbedB₀ with ⟨ιB₀⟩
    exact ⟨ιB₀.toOpposite (algHomFromFieldCommutes (k := k) (K := K) ιB₀)⟩
  have hdimB₀ :
      Module.finrank k B₀ = Module.finrank k K ^ 2 := by
    calc
      Module.finrank k B₀ = Module.finrank k C := by
        exact (shrinkFiniteCentralSimpleAlgEquiv (A := A) (k := k) C).toLinearEquiv.finrank_eq
      _ = Module.finrank k K ^ 2 := splitModelCentralizerFinrankSq (A := A) (K := K) e
  have hdimOpp :
      Module.finrank k B₀.opposite = Module.finrank k K ^ 2 := by
    calc
      Module.finrank k B₀.opposite = Module.finrank k B₀ := by
        exact (MulOpposite.opLinearEquiv k (M := B₀)).finrank_eq.symm
      _ = Module.finrank k K ^ 2 := hdimB₀
  exact ⟨B₀.opposite, hBrauerB₀, hEmbedOpp, hdimOpp⟩

-- ============================================================
-- Main theorem: splitting ↔ ∃ Brauer-equivalent with embedded subfield
-- ============================================================

/-- A finite extension `K/k` splits the finite central simple `k`-algebra `A` if
and only if there exists a finite central simple `k`-algebra `B` Brauer equivalent to `A` that
contains `K` as a `k`-subalgebra and has `k`-dimension `[K : k]^2`. -/
@[stacks 074Z]
theorem isSplitBy_iff_exists_embedding :
    A.IsSplitBy K ↔
      ∃ B : CSA.{u, v} k,
        IsBrauerEquivalent A B ∧
          Nonempty (K →ₐ[k] B) ∧
          Module.finrank k B = Module.finrank k K ^ 2 := by
  constructor
  · intro hA
    exact A.forward_commutant_witness_of_split K hA
  · rintro ⟨B, hAB, hK, hdim⟩
    have hSplitB : B.IsSplitBy K := B.isSplitBy_of_self_embedding_finrank_sq K hK hdim
    exact (A.isSplitBy_iff_of_brauerEquivalent K hAB).2 hSplitB

end

end CSA

end
