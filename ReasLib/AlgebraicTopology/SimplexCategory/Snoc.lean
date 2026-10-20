module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Terminal extension of simplex morphisms

@stack 0192

This leaf owns the order-theoretic operation of adjoining a terminal source vertex to a simplex
morphism.  `snoc` keeps the target fixed, while `extendLast` also adjoins the terminal target
vertex.  The construction is independent of Eilenberg--MacLane objects; those objects only use
the bundled epi consequences in their source-oriented index API.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.Hom

/-- Adjoin a terminal source vertex and send it to the terminal target vertex. -/
@[stacks 0192 "terminal extension of a simplex morphism"]
def snoc {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) : ⦋n + 1⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.mkHom
    { toFun := Fin.snoc f.toOrderHom (Fin.last m)
      monotone' := sorry }

/-- The terminal extension agrees with `f` on the old source vertices. -/
@[simp, stacks 0192 "terminal extension on old simplex vertices"]
theorem snoc_apply_castSucc {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    (snoc f).toOrderHom i.castSucc = f.toOrderHom i := sorry

/-- The terminal extension sends the new source vertex to the terminal target vertex. -/
@[simp, stacks 0192 "terminal extension on the new simplex vertex"]
theorem snoc_apply_last {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (snoc f).toOrderHom (Fin.last (n + 1)) = Fin.last m := sorry

/-- Restricting a terminal extension along the final coface recovers the original map. -/
@[simp, stacks 0192 "final coface restriction of a terminal extension"]
theorem δ_last_comp_snoc {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ snoc f = f := sorry

/-- Adjoining the terminal source vertex preserves an epic simplex morphism. -/
@[stacks 0192 "epic terminal extension of a simplex morphism"]
theorem snoc_epi {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] : Epi (snoc f) := sorry

/-- Extend a simplex morphism to the terminal vertices in both source and target. -/
@[stacks 0192 "two-sided terminal extension of a simplex morphism"]
def extendLast {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    ⦋n + 1⦌ ⟶ ⦋m + 1⦌ :=
  snoc (f ≫ SimplexCategory.δ (Fin.last (m + 1)))

/-- The two-sided terminal extension agrees with `f` on old source vertices. -/
@[simp, stacks 0192 "two-sided terminal extension on old vertices"]
theorem extendLast_apply_castSucc {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    (extendLast f).toOrderHom i.castSucc = (f.toOrderHom i).castSucc := sorry

/-- The two-sided terminal extension sends the new source vertex to the new target vertex. -/
@[simp, stacks 0192 "two-sided terminal extension on new vertices"]
theorem extendLast_apply_last {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (extendLast f).toOrderHom (Fin.last (n + 1)) = Fin.last (m + 1) := sorry

/-- Extending an epic simplex morphism at both terminal vertices remains epic. -/
@[stacks 0192 "epic two-sided terminal extension of a simplex morphism"]
theorem extendLast_epi {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] : Epi (extendLast f) := sorry

end SimplexCategory.Hom
