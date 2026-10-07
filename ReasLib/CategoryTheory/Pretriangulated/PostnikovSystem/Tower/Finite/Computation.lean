module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Finite.Objects
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Triangle

/-!
# Computations for Finite Restrictions of Postnikov Towers

This leaf identifies every object and structural map of the canonical finite
restriction with the corresponding component of the sequential tower.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Truncating a successor finite row recovers the preceding finite row. -/
@[simp, stacks 0D8Z "successor compatibility of finite Postnikov rows"]
theorem row_succ_δ₀ (T : Tower D) (n : ℕ) :
    (T.row (n + 1)).δ₀ = T.row n := sorry

/-- The recursive tail of a successor finite restriction is the preceding finite restriction. -/
@[simp, stacks 0D8Z "successor compatibility of finite Postnikov systems"]
theorem finite_succ_tail (T : Tower D) (n : ℕ) :
    (T.finite (n + 1)).tail = T.finite n := sorry

/-- The reversed finite row of length zero consists only of the zeroth tower object. -/
@[simp]
theorem row_zero (T : Tower D) :
    T.row 0 = ComposableArrows.mk₀ (T.X 0) := sorry

/-- A successor finite row is obtained by adjoining the next tower differential on the left. -/
theorem row_succ (T : Tower D) (n : ℕ) :
    T.row (n + 1) =
      (T.row n).precomp (T.d n ≫ eqToHom (T.row_left n).symm) := sorry

/-- The head comparison of a finite restriction is the tower comparison, up to its canonical
endpoint identifications. -/
theorem finite_headToX (T : Tower D) (n : ℕ) :
    (T.finite n).headToX =
      eqToHom (T.finite_head n) ≫ T.toX n ≫ eqToHom (T.row_left n).symm := sorry

namespace Finite

/-- A successor map of the finite row is the corresponding tower differential, up to canonical
endpoint identifications. This theorem is intentionally not a simp rule: its normal form contains
endpoint transports. -/
theorem rowMap (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.row n).map' i.1 (i.1 + 1) =
      eqToHom (rowSource T n i) ≫ T.d (index i) ≫
        eqToHom (rowTarget T n i).symm := sorry

/-- The comparison map of a finite restriction is the tower comparison at the corresponding
index, up to canonical endpoint identifications. This theorem is intentionally not a simp rule. -/
theorem toX (T : Tower D) (n : ℕ) (i : Fin (n + 1)) :
    (T.finite n).toX i =
      eqToHom (auxObj T n i) ≫ T.toX (index i) ≫ eqToHom (rowObj T n i).symm := sorry

/-- A second map of the finite Postnikov system is the corresponding tower map, up to canonical
endpoint identifications. This theorem is intentionally not a simp rule. -/
theorem toNext (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.finite n).toNext i =
      eqToHom (rowSource T n i) ≫ T.toNext (index i) ≫
        eqToHom (auxTarget T n i).symm := sorry

/-- A connecting map of the finite Postnikov system is the corresponding tower map, up to
canonical endpoint identifications. This theorem is intentionally not a simp rule. -/
theorem connecting (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.finite n).connecting i =
      eqToHom (auxTarget T n i) ≫ T.connecting (index i) ≫
        (eqToHom (auxSource T n i).symm)⟦(1 : ℤ)⟧' := sorry

/-- A stage triangle of a finite restriction is the corresponding triangle of the tower.
This theorem is intentionally not a simp rule because the identification transports all three
vertices along the reversed finite indexing. -/
@[stacks 0D8Z "stage triangle of a finite Postnikov-tower restriction"]
theorem triangle (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.finite n).triangle i = T.triangle (index i) := sorry

end Finite

end CategoryTheory.PostnikovSystem.Tower
