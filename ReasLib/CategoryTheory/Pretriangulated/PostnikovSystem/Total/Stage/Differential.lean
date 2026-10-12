/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Stage.Basic

/-!
# Differentials of Total Finite Postnikov Systems

This leaf exposes the adjacent arrows of the underlying finite row as natural transformations.
It also records the stagewise factorization supplied by the Postnikov-system structure.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- The adjacent arrow of the underlying finite row as a natural transformation between
consecutive row-evaluation functors. -/
@[stacks 0D7Z "differential of a total finite Postnikov-system row"]
def d (n : ℕ) (i : Fin n) : row D n i.castSucc ⟶ row D n i.succ :=
  Functor.whiskerLeft (forget D n)
    ((evaluation (Fin (n + 1)) D).map (homOfLE i.castSucc_le_succ))

/-- The component of the row differential is the corresponding adjacent arrow of the finite
row. -/
@[simp, stacks 0D7Z]
theorem d_app (n : ℕ) (i : Fin n) (P : Total D n) :
    (d D n i).app P = P.base.map' i.1 i.1.succ := sorry

/-- Row differentials commute with every morphism in the total category. -/
@[reassoc, stacks 0D7Z "naturality of the total Postnikov-system differential"]
theorem d_naturality (n : ℕ) (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    (row D n i.castSucc).map f ≫ (d D n i).app Q =
      (d D n i).app P ≫ (row D n i.succ).map f := sorry

variable (D) in
/-- At every finite stage, the second triangle map followed by the auxiliary-to-row comparison
is the corresponding row differential. -/
@[stacks 0D7Z "factorization of a total Postnikov-system differential"]
theorem toNext_comp_toRow (n : ℕ) (i : Fin n) :
    toNext D n i ≫ toRow D n i.succ = d D n i := sorry

end CategoryTheory.PostnikovSystem.Total
