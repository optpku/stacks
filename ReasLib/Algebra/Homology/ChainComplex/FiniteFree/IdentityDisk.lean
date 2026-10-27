/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.Disk
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinate identity disks

`ChainComplex.disk` is the representation-independent two-term identity
complex.  This leaf adds the explicit `Fin`-coordinate presentation used by
finite-free matrix arguments.  The coordinate rank and matrix are concrete
data owners; the chapter-level name is retained as a presentation bridge,
not as a second abstract disk API.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

namespace FiniteFreeComplex

variable {e : ℕ}

section

variable {R : Type u} [Ring R]

/-- The abstract identity disk attached to a rank-one coordinate module. -/
@[stacks 0192 "finite-free identity disk specialization"]
noncomputable abbrev identityDisk (i : Fin e) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.disk (ModuleCat.of R (Fin 1 → R)) i.1

/-- The rank of the explicit coordinate identity disk in degree `j`. -/
@[stacks 0192 "identity-disk coordinate rank"]
def identityDiskRank (i : Fin e) (j : ℕ) : ℕ :=
  if j = i.1 + 1 ∨ j = i.1 then 1 else 0

/-- The matrix of the explicit identity-disk differential in degree `j`. -/
@[stacks 0192 "identity-disk coordinate matrix"]
def identityDiskMatrix (i : Fin e) (j : ℕ) :
    Matrix (Fin (identityDiskRank i (j + 1))) (Fin (identityDiskRank i j)) R :=
  fun _ _ ↦ if j = i.1 then 1 else 0

/-- The coordinate differential of the identity disk. -/
@[stacks 0192 "identity-disk coordinate differential"]
abbrev identityDiskDifferential (i : Fin e) (j : ℕ) :
    ModuleCat.of R (Fin (identityDiskRank i (j + 1)) → R) ⟶
      ModuleCat.of R (Fin (identityDiskRank i j) → R) :=
  ModuleCat.ofHom ((identityDiskMatrix i j).toLinearMapRight')

namespace identityDiskDifferential

/-- The coordinate identity-disk differential vanishes away from its supported degree. -/
@[stacks 0192 "identity-disk differential off support"]
theorem eq_zero_of_ne (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
    identityDiskDifferential i j =
      (0 :
        ModuleCat.of R (Fin (identityDiskRank i (j + 1)) → R) ⟶
          ModuleCat.of R (Fin (identityDiskRank i j) → R)) := by
  have hM : identityDiskMatrix (R := R) i j = 0 := by
    ext a b
    simp [identityDiskMatrix, hj]
  simp [identityDiskDifferential, hM]

/-- Consecutive coordinate differentials in an identity disk compose to zero. -/
@[simp, stacks 0192 "identity-disk differential squares to zero"]
theorem sq (i : Fin e) (j : ℕ) :
    identityDiskDifferential i (j + 1) ≫ identityDiskDifferential i j =
      (0 :
        ModuleCat.of R (Fin (identityDiskRank i (j + 2)) → R) ⟶
          ModuleCat.of R (Fin (identityDiskRank i j) → R)) := by
  by_cases hj : j = i.1
  · have hSucc : j + 1 ≠ i.1 := by omega
    rw [eq_zero_of_ne i hSucc, zero_comp]
  · rw [eq_zero_of_ne i hj, comp_zero]

end identityDiskDifferential

/-- The explicit finite-coordinate presentation of the identity disk. -/
@[stacks 0192 "coordinate identity-disk complex"]
def identityDiskComplex (i : Fin e) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (fun j ↦ ModuleCat.of R (Fin (identityDiskRank i j) → R))
    (identityDiskDifferential i)
    (identityDiskDifferential.sq i)

namespace identityDiskRank

/-- Away from the supported degrees `i + 1` and `i`, the identity-disk rank is zero. -/
@[simp, stacks 0192 "identity-disk rank off support"]
theorem eq_zero_of_ne_support
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    identityDiskRank i j = 0 := by
  simp [identityDiskRank, hjSucc, hjCast]

/-- The supported source degree of a coordinate identity disk has rank one. -/
@[simp, stacks 0192 "identity-disk source rank"]
theorem succ (i : Fin e) :
    identityDiskRank i (i.1 + 1) = 1 := by
  simp [identityDiskRank]

/-- The supported target degree of a coordinate identity disk has rank one. -/
@[simp, stacks 0192 "identity-disk target rank"]
theorem castSucc (i : Fin e) :
    identityDiskRank i i.1 = 1 := by
  simp [identityDiskRank]

end identityDiskRank

namespace identityDiskComplex

/-- Away from the supported degrees, the coordinate identity disk has a zero term. -/
@[stacks 0192 "identity-disk zero term off support"]
theorem isZero_X_of_ne_support
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    IsZero ((FiniteFreeComplex.identityDiskComplex (R := R) i).X j) := by
  change IsZero (ModuleCat.of R (Fin (identityDiskRank i j) → R))
  rw [identityDiskRank.eq_zero_of_ne_support i hjSucc hjCast]
  exact ModuleCat.isZero_of_subsingleton _

/-- The upper supported term of the coordinate identity disk is the rank-one standard module. -/
@[stacks 0192 "identity-disk upper supported term"]
theorem X_eq_succ (i : Fin e) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X (i.1 + 1) =
      ModuleCat.of R (Fin 1 → R) := by
  change ModuleCat.of R (Fin (identityDiskRank i (i.1 + 1)) → R) = _
  rw [identityDiskRank.succ]

/-- The lower supported term of the coordinate identity disk is the rank-one standard module. -/
@[stacks 0192 "identity-disk lower supported term"]
theorem X_eq_castSucc (i : Fin e) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).X i.1 =
      ModuleCat.of R (Fin 1 → R) := by
  change ModuleCat.of R (Fin (identityDiskRank i i.1) → R) = _
  rw [identityDiskRank.castSucc]

/-- The coordinate identity-disk differential is zero away from its supported degree. -/
@[stacks 0192 "identity-disk differential off supported degree"]
theorem d_eq_zero_of_ne (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
    (FiniteFreeComplex.identityDiskComplex (R := R) i).d (j + 1) j = 0 := by
  change ChainComplex.of.d
    (fun n ↦ ModuleCat.of R (Fin (identityDiskRank i n) → R))
    (identityDiskDifferential i) (j + 1) j = 0
  rw [ChainComplex.of_d]
  exact identityDiskDifferential.eq_zero_of_ne i hj

/-- After the supported terms are identified with the rank-one module, the disk differential is
the canonical identity morphism. -/
@[stacks 0192 "identity-disk supported differential bridge"]
theorem eqToHom_symm_comp_d (i : Fin e) :
    eqToHom (X_eq_succ (R := R) (e := e) i).symm ≫
        (FiniteFreeComplex.identityDiskComplex (R := R) i).d (i.1 + 1) i.1 =
      eqToHom (X_eq_castSucc (R := R) (e := e) i).symm := by
  have transport (a b : ℕ) (ha : a = 1) (hb : b = 1)
      (M : Matrix (Fin a) (Fin b) R) (hM : ∀ x y, M x y = 1) :
      eqToHom (congrArg (fun n ↦ ModuleCat.of R (Fin n → R)) ha).symm ≫
          ModuleCat.ofHom M.toLinearMapRight' =
        eqToHom (congrArg (fun n ↦ ModuleCat.of R (Fin n → R)) hb).symm := by
    subst a b
    have hMatrix : M = 1 := by
      ext x y
      simp [Matrix.one_apply, hM, Subsingleton.elim x y]
    simp [hMatrix]
  change eqToHom (X_eq_succ (R := R) i).symm ≫
      ChainComplex.of.d
        (fun n ↦ ModuleCat.of R (Fin (identityDiskRank i n) → R))
        (identityDiskDifferential i) (i.1 + 1) i.1 = _
  rw [ChainComplex.of_d]
  exact transport _ _ (identityDiskRank.succ i) (identityDiskRank.castSucc i)
    (identityDiskMatrix i i.1) (by intros; simp [identityDiskMatrix])

end identityDiskComplex

end

end FiniteFreeComplex

end
