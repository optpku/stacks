module

public import ReasLib.Algebra.CentralSimple.Splitting.Criterion
public import ReasLib.Algebra.CentralSimple.BrauerGroup.Degree
public import ReasLib.Algebra.CentralSimple.BrauerGroup.DivisionRepresentative

/-! # Degree Divisibility for Splitting Fields

The degree of a central simple algebra divides the degree of every finite splitting
field extension.

## Main declarations

- `CSA.degree_dvd_finrank_splittingField` — `degree A ∣ [k' : k]` for every splitting field `k'`

## References

- [Stacks Project, Tag 0751](https://stacks.math.columbia.edu/tag/0751)
-/

@[expose] public section

universe u v w

section

open Matrix

variable {k : Type u} [Field k]
variable {K : Type v} [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
variable [Algebra.IsCentral k K]
variable {k' : Type w} [Field k'] [Algebra k k'] [FiniteDimensional k k']

/-- If a matrix algebra over a division ring is central over `k`, then
the underlying division ring is central over `k`. -/
private lemma matrix_central_implies_division_central' (n : ℕ) [NeZero n] (D : Type v)
    [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) D)] :
    Algebra.IsCentral k D := by
  refine ⟨fun x hx ↦ ?_⟩
  have hxM : scalar (Fin n) x ∈ (Subalgebra.center k D).map (scalarAlgHom (Fin n) k) := by
    exact ⟨x, hx, rfl⟩
  rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have := congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha; simp [Matrix.scalar_apply, i] at this; exact this.symm

/-- A matrix presentation of a finite central simple algebra over a division ring
yields Brauer equivalence with the corresponding division-algebra representative. -/
private lemma matrix_model_isBrauerEquivalent_division'
    {B : CSA.{u, v} k} {n : ℕ} [NeZero n] {D : Type v}
    [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
    [Algebra.IsCentral k D]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) D)]
    (e : B ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
  refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
  exact ⟨((reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩

/-- Brauer-equivalent finite central division algebras have the same dimension
over the base field. -/
private lemma finrank_eq_of_division_brauer_similarity
    {D : Type v} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
    [Algebra.IsCentral k D]
    (h :
      IsBrauerEquivalent (CSA.mk (AlgCat.of k K)) (CSA.mk (AlgCat.of k D))) :
    Module.finrank k D = Module.finrank k K := by
  rcases (brauerEquivalent_divisionAlgebra_iff k K D).1 h with ⟨eKD⟩
  simpa using (LinearEquiv.finrank_eq eKD.toLinearEquiv).symm

/-- If `a² = (n d)²`, then `d` divides `a`. -/
private lemma dvd_of_square_factorization {a n d : ℕ} (h : a ^ 2 = (n * d) ^ 2) : d ∣ a := by
  refine ⟨n, ?_⟩
  calc
    a = Nat.sqrt (a ^ 2) := by
      simp [pow_two]
    _ = Nat.sqrt ((n * d) ^ 2) := by rw [h]
    _ = n * d := by
      simp [pow_two]
    _ = d * n := by
      rw [Nat.mul_comm]

/-- The degree of the central simple algebra attached to a finite central skew field
`K/k` divides the degree of every finite splitting field. -/
@[stacks 0751]
lemma CSA.degree_dvd_finrank_splittingField
    (hk' : (CSA.mk (AlgCat.of k K)).IsSplitBy k') :
    (CSA.mk (AlgCat.of k K)).degree ∣ Module.finrank k k' :=
  by
    let A : CSA.{u, v} k := CSA.mk (AlgCat.of k K)
    rcases (A.isSplitBy_iff_exists_embedding k').1 hk' with
      ⟨B, hAB, _, hdim⟩
    letI : IsArtinianRing B := IsArtinianRing.of_finite k B
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
    letI : NeZero n := hn
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : Module.Finite k D := hDfin
    letI : FiniteDimensional k D := inferInstance
    letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) := Algebra.IsCentral.of_algEquiv k B _ e
    letI : Algebra.IsCentral k D := matrix_central_implies_division_central' (k := k) n D
    have hBD : IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) :=
      matrix_model_isBrauerEquivalent_division' (k := k) e
    have hfinD : Module.finrank k D = Module.finrank k K :=
      finrank_eq_of_division_brauer_similarity (k := k) (K := K)
        (IsBrauerEquivalent.trans hAB hBD)
    have hsq : Module.finrank k k' ^ 2 = (n * A.degree) ^ 2 := by
      calc
        Module.finrank k k' ^ 2 = Module.finrank k B := hdim.symm
        _ = Module.finrank k (Matrix (Fin n) (Fin n) D) := LinearEquiv.finrank_eq e.toLinearEquiv
        _ = n * n * Module.finrank k D := by
          simpa using (Module.finrank_matrix k D (Fin n) (Fin n))
        _ = n * n * A.degree ^ 2 := by rw [hfinD, A.degree_sq_eq_finrank]
        _ = (n * A.degree) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    exact dvd_of_square_factorization hsq

end

end
