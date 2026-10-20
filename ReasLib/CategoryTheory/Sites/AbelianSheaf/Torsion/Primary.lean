/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.Algebra.Field.Defs

@[expose] public section

open CategoryTheory Opposite

universe w v u t

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An abelian sheaf is locally `p`-power torsion if every section admits a cover on
which each restriction is annihilated by a power of `p`. -/
def IsLocallyPPowerTorsion (p : ℕ) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (sectionValue : F.obj.obj (op U)),
    ∃ cover : J.Cover U, ∀ arrow : cover.Arrow,
      ∃ exponent : ℕ, (p ^ exponent) • F.obj.map arrow.f.op sectionValue = 0

/-- An abelian sheaf is locally prime-to-characteristic torsion over a field `k` if
every section admits a cover on which each restriction is annihilated by a nonzero
natural number whose image in `k` is a unit. -/
def IsLocallyPrimeToCharTorsion (k : Type t) [Field k]
    (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (sectionValue : F.obj.obj (op U)),
    ∃ cover : J.Cover U, ∀ arrow : cover.Arrow,
      ∃ order : ℕ, order ≠ 0 ∧ IsUnit (order : k) ∧
        order • F.obj.map arrow.f.op sectionValue = 0

end CategoryTheory.Sheaf
