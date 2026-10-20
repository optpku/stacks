module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural

/-!
# Positive endofunctor iteration

This leaf owns the source-facing positive iterate notation and the canonical comparisons that
split positive iterates into consecutive blocks.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctor

/-- The left-associated `(n + 1)`-fold positive composite of an endofunctor. -/
@[stacks 0G5M]
def obj (Y : C ⥤ C) (n : ℕ) : C ⥤ C := Endofunctor.iterate Y (n + 1)

scoped[CategoryTheory.IteratedEndofunctor]
  notation3:1000 Y " ⁺⦋" n "⦌" => IteratedEndofunctor.obj Y n

open scoped CategoryTheory.IteratedEndofunctor

/-- A positive iterate agrees with repeated postcomposition starting from `Y`. -/
@[stacks 0G5M "positive iterate comparison"]
theorem obj.eq_natIterate (Y : C ⥤ C) (n : ℕ) :
    Y ⁺⦋n⦌ = Nat.iterate (fun F : C ⥤ C ↦ F ⋙ Y) n Y := sorry

/-- Prepending one copy of an endofunctor to a positive iterate canonically gives the next
positive iterate. -/
@[stacks 0G5M "prepending an endofunctor to a positive iterate"]
def prependIso (Y : C ⥤ C) (n : ℕ) :
    Y ⋙ Y ⁺⦋n⦌ ≅ Y ⁺⦋n + 1⦌ :=
  Functor.isoWhiskerRight (Endofunctor.iterate.oneIso Y).symm (Y ⁺⦋n⦌) ≪≫
    (Endofunctor.iterate.addIso Y 1 (n + 1)).symm ≪≫
    Endofunctor.iterate.indexIso Y (Nat.add_comm 1 (n + 1))

/-- The canonical comparison splitting the `(n + m + 1)`-fold iterate into the `n`-th and
`m`-th positive iterates. -/
@[stacks 0G5M "positive iterate factorization"]
def compIso (Y : C ⥤ C) (n m : ℕ) :
    Y ⁺⦋n + m + 1⦌ ≅ (Y ⁺⦋n⦌) ⋙ Y ⁺⦋m⦌ :=
  Endofunctor.iterate.indexIso Y
      (congrArg (fun k : ℕ ↦ k + 1) (Nat.add_right_comm n m 1)) ≪≫
    Endofunctor.iterate.addIso Y (n + 1) (m + 1)

/-- Split the `(n + 2)`-fold positive iterate immediately before the block indexed by `j` from
the right.  The two factors contain `n - j + 1` and `j + 1` copies of `Y`, respectively. -/
@[stacks 0G5S "splitting a positive endofunctor iterate at an interior position"]
def splitIso (Y : C ⥤ C) (n : ℕ) (j : Fin (n + 1)) :
    Y ⁺⦋n + 1⦌ ≅ (Y ⁺⦋n - j.1⦌) ⋙ Y ⁺⦋j.1⦌ :=
  eqToIso (congrArg (IteratedEndofunctor.obj Y)
      (congrArg (fun k : ℕ ↦ k + 1)
        (Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt))).symm) ≪≫
    compIso Y (n - j.1) j.1

end IteratedEndofunctor

end CategoryTheory
