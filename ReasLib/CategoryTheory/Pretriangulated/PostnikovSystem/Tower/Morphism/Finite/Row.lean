/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Finite.Computation
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Basic

/-!
# Finite-Row Restrictions of Postnikov-Tower Morphisms

This leaf restricts a componentwise tower morphism to each reversed finite row
and provides recursive and pointwise computation rules.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Hom

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T T' T'' : Tower D}

namespace Core

/-- Internal components of finite-row restriction, synchronized with `Tower.Core.rows`. -/
def rowApp (f : Hom T T') :
    (n : ℕ) → ∀ i : Fin (n + 1), (T.row n).obj i ⟶ (T'.row n).obj i
  | 0 => fun i => Fin.cases (f.xMap 0) (fun j => Fin.elim0 j) i
  | n + 1 => fun i => Fin.cases (f.xMap (n + 1)) (rowApp f n) i

/-- Consecutive internal row components commute with the finite-row maps. -/
theorem rowApp_naturality (f : Hom T T') (n : ℕ) (i : Fin n) :
    (T.row n).map' i.1 (i.1 + 1) ≫ rowApp f n i.succ =
      rowApp f n i.castSucc ≫ (T'.row n).map' i.1 (i.1 + 1) := sorry

end Core

/-- Restrict a tower morphism to its reversed finite rows. -/
@[stacks 0D8Z "finite-row restriction of a Postnikov tower morphism"]
def row (f : Hom T T') (n : ℕ) : T.row n ⟶ T'.row n :=
  ComposableArrows.homMk (Core.rowApp f n)
    (fun i hi => Core.rowApp_naturality f n ⟨i, hi⟩)

/-- At length zero, finite-row restriction uses the zeroth row-object component directly. -/
@[simp 1100]
theorem row_zero_app (f : Hom T T') :
    (row f 0).app 0 = f.xMap 0 := sorry

/-- The new leftmost component of a successor finite-row restriction is the corresponding
row-object component of the tower morphism. -/
@[simp 1100]
theorem row_succ_app_zero (f : Hom T T') (n : ℕ) :
    (row f (n + 1)).app 0 = f.xMap (n + 1) := sorry

/-- Away from the new left endpoint, a successor finite-row restriction reuses the preceding
finite-row restriction. -/
@[simp 1100]
theorem row_succ_app_succ (f : Hom T T') (n : ℕ) (i : Fin (n + 1)) :
    (row f (n + 1)).app i.succ = (row f n).app i := sorry

/-- Truncating the successor finite-row restriction of a tower morphism recovers the preceding
finite-row restriction. -/
@[simp, stacks 0D8Z "successor compatibility of finite-row morphisms"]
theorem row_succ_δ₀ (f : Hom T T') (n : ℕ) :
    ComposableArrows.δ₀Functor.map (row f (n + 1)) = row f n := sorry

/-- A finite-row component is the corresponding transported `xMap`. This theorem is intentionally
not a simp rule because its normal form contains endpoint transports. -/
@[stacks 0D8Z]
theorem row_app (f : Hom T T') (n : ℕ) (i : Fin (n + 1)) :
    (row f n).app i =
      eqToHom (Tower.Finite.rowObj T n i) ≫ f.xMap (Tower.Finite.index i) ≫
        eqToHom (Tower.Finite.rowObj T' n i).symm := sorry

/-- Restriction of an identity tower morphism is an identity finite-row morphism. -/
@[simp]
theorem id_row (T : Tower D) (n : ℕ) : row (id T) n = 𝟙 (T.row n) := sorry

/-- Restriction to finite rows preserves composition. -/
@[simp]
theorem comp_row (f : Hom T T') (g : Hom T' T'') (n : ℕ) :
    row (comp f g) n = row f n ≫ row g n := sorry

end CategoryTheory.PostnikovSystem.Tower.Hom
