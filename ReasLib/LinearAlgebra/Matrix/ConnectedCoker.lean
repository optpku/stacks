/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.LinearAlgebra.BilinearForm.AdjointCoker
public import ReasLib.LinearAlgebra.BilinearForm.IntegralLattice
public import ReasLib.LinearAlgebra.Matrix.NegativeSemidefinite

@[expose] public section

open scoped BigOperators

universe u

namespace AddSubgroup.torsionBy

/-- The canonical `ZMod n`-module structure on the subgroup killed by `n`. -/
instance instModuleZMod {G : Type u} [AddCommGroup G] {n : ℕ} :
    Module (ZMod n) (AddSubgroup.torsionBy G (n : ℤ)) :=
  AddSubgroup.torsionBy.zmodModule

end AddSubgroup.torsionBy

namespace Matrix

/-- For a connected symmetric integer matrix with nonnegative off-diagonal
entries and a positive integral kernel vector, the `ℓ`-torsion in its cokernel
has `ZMod ℓ`-dimension at most the number of positive entries strictly above
the diagonal plus `1 - n`, provided `ℓ` is coprime to every matrix entry and
every coordinate of the kernel vector. -/
theorem finrank_torsionBy_coker_le_cycleRank
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ)
    (h_symmetric : A.IsSymm)
    (h_offDiagonal : ∀ i j, i ≠ j → 0 ≤ A i j)
    (h_positive : ∀ i, 0 < m i)
    (h_kernel : A *ᵥ m = 0)
    (h_connected : ∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h_coprime_entries : ∀ i j, Nat.Coprime ℓ (A i j).natAbs)
    (h_coprime_weights : ∀ i, Nat.Coprime ℓ (m i).natAbs) :
    Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy
          ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) (ℓ : ℤ)) ≤
      (Finset.univ.filter fun ij : Fin n × Fin n ↦
        ij.1 < ij.2 ∧ 0 < A ij.1 ij.2).card + 1 - n := sorry

end Matrix
