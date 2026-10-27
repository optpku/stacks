/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
    (T.row (n + 1)).δ₀ = T.row n := rfl

/-- The recursive tail of a successor finite restriction is the preceding finite restriction. -/
@[simp, stacks 0D8Z "successor compatibility of finite Postnikov systems"]
theorem finite_succ_tail (T : Tower D) (n : ℕ) :
    (T.finite (n + 1)).tail = T.finite n := rfl

/-- The reversed finite row of length zero consists only of the zeroth tower object. -/
@[simp]
theorem row_zero (T : Tower D) :
    T.row 0 = ComposableArrows.mk₀ (T.X 0) := rfl

/-- A successor finite row is obtained by adjoining the next tower differential on the left. -/
theorem row_succ (T : Tower D) (n : ℕ) :
    T.row (n + 1) =
      (T.row n).precomp (T.d n ≫ eqToHom (T.row_left n).symm) := rfl

/-- The head comparison of a finite restriction is the tower comparison, up to its canonical
endpoint identifications. -/
theorem finite_headToX (T : Tower D) (n : ℕ) :
    (T.finite n).headToX =
      eqToHom (T.finite_head n) ≫ T.toX n ≫ eqToHom (T.row_left n).symm := by
  cases n with
  | zero =>
      change T.toX 0 = 𝟙 _ ≫ T.toX 0 ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  | succ n =>
      change T.toX (n + 1) = 𝟙 _ ≫ T.toX (n + 1) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]

namespace Finite

/-- A successor map of the finite row is the corresponding tower differential, up to canonical
endpoint identifications. This theorem is intentionally not a simp rule: its normal form contains
endpoint transports. -/
theorem rowMap (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.row n).map' i.1 (i.1 + 1) =
      eqToHom (rowSource T n i) ≫ T.d (index i) ≫
        eqToHom (rowTarget T n i).symm := by
  apply (conj_eqToHom_iff_heq _ _ (rowSource T n i) (rowTarget T n i)).2
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact comp_eqToHom_heq _ _
      · change HEq ((T.row n).map' j.1 (j.1 + 1)) (T.d (index j.succ))
        rw [show index j.succ = index j by
          simp only [index, Fin.rev_succ, Fin.val_castSucc]]
        exact ih j

/-- The comparison map of a finite restriction is the tower comparison at the corresponding
index, up to canonical endpoint identifications. This theorem is intentionally not a simp rule. -/
theorem toX (T : Tower D) (n : ℕ) (i : Fin (n + 1)) :
    (T.finite n).toX i =
      eqToHom (auxObj T n i) ≫ T.toX (index i) ≫ eqToHom (rowObj T n i).symm := by
  apply (conj_eqToHom_iff_heq _ _ (auxObj T n i) (rowObj T n i)).2
  induction n with
  | zero =>
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      rfl
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change HEq ((T.finite n).toX j) (T.toX (index j.succ))
        rw [show index j.succ = index j by
          simp only [index, Fin.rev_succ, Fin.val_castSucc]]
        exact ih j

/-- A second map of the finite Postnikov system is the corresponding tower map, up to canonical
endpoint identifications. This theorem is intentionally not a simp rule. -/
theorem toNext (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.finite n).toNext i =
      eqToHom (rowSource T n i) ≫ T.toNext (index i) ≫
        eqToHom (auxTarget T n i).symm := by
  apply (conj_eqToHom_iff_heq _ _ (rowSource T n i) (auxTarget T n i)).2
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · cases n <;> exact comp_eqToHom_heq _ _
      · cases n with
        | zero => exact Fin.elim0 j
        | succ n =>
            change HEq ((T.finite (n + 1)).toNext j) (T.toNext (index j.succ))
            rw [show index j.succ = index j by
              simp only [index, Fin.rev_succ, Fin.val_castSucc]]
            exact ih j

/-- A connecting map of the finite Postnikov system is the corresponding tower map, up to
canonical endpoint identifications. This theorem is intentionally not a simp rule. -/
theorem connecting (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.finite n).connecting i =
      eqToHom (auxTarget T n i) ≫ T.connecting (index i) ≫
        (eqToHom (auxSource T n i).symm)⟦(1 : ℤ)⟧' := by
  rw [eqToHom_map]
  apply (conj_eqToHom_iff_heq' _ _ (auxTarget T n i)
    (congrArg (shiftFunctor D (1 : ℤ)).obj (auxSource T n i).symm)).2
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · cases n <;> exact eqToHom_comp_heq _ _
      · cases n with
        | zero => exact Fin.elim0 j
        | succ n =>
            change HEq ((T.finite (n + 1)).connecting j) (T.connecting (index j.succ))
            rw [show index j.succ = index j by
              simp only [index, Fin.rev_succ, Fin.val_castSucc]]
            exact ih j

omit [Limits.HasZeroObject D] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [Pretriangulated D] in
private theorem triangle_mk_transport_third {A B C C' : D} (h : C = C')
    (f : A ⟶ B) (g : B ⟶ C') (k : C' ⟶ A⟦(1 : ℤ)⟧) :
    Triangle.mk f (g ≫ eqToHom h.symm) (eqToHom h ≫ k) = Triangle.mk f g k := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- A stage triangle of a finite restriction is the corresponding triangle of the tower.
This theorem is intentionally not a simp rule because the identification transports all three
vertices along the reversed finite indexing. -/
@[stacks 0D8Z "stage triangle of a finite Postnikov-tower restriction"]
theorem triangle (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.finite n).triangle i = T.triangle (index i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · cases n <;> exact triangle_mk_transport_third _ _ _ _
      · cases n with
        | zero => exact Fin.elim0 j
        | succ n =>
            change (T.finite (n + 1)).triangle j = T.triangle (index j.succ)
            simpa only [index, Fin.rev_succ, Fin.val_castSucc] using ih j

end Finite

end CategoryTheory.PostnikovSystem.Tower
