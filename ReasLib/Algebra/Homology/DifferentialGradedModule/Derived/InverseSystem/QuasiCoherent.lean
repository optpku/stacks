/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.Transition
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherent objects in the derived category of DG-module systems

For a global derived module system, the adjacent comparison is the adjoint of its original
`A (n + 1)`-linear transition.  These comparisons descend through the global localization.
Quasi-coherent objects are those for which every descended comparison is invertible.
-/

@[expose] public section

noncomputable section

universe u x

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.Derived

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- On ordinary DG-module systems, the adjacent extension comparison is the successor
specialization of the comparison over arbitrary index inequalities. -/
@[stacks 0GZ9 "adjacent comparison before global localization"]
noncomputable abbrev comparisonSource
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    stageSource A (n + 1) ⋙
        CochainDGAlgebra.Hom.Derived.extension
          (A.stepMap n) ⟶
      stageSource A n :=
  comparisonSourceLE A (Nat.le_succ n)

/-- The adjacent derived extension comparison on the global category `D(ℕ, A)`. -/
@[stacks 0GZ9 "adjacent comparison for a derived DG-module system"]
noncomputable abbrev comparison
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    eval A (n + 1) ⋙
        CochainDGAlgebra.Hom.Derived.extension
          (A.stepMap n) ⟶
      eval A n :=
  comparisonLE A (Nat.le_succ n)

/-- The arbitrary source comparison at a successor inequality is the adjacent comparison. -/
@[simp]
theorem comparisonSourceLE_succ
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    comparisonSourceLE A (Nat.le_succ n) = comparisonSource A n := sorry

/-- The arbitrary descended comparison at a successor inequality is the adjacent comparison. -/
@[simp]
theorem comparisonLE_succ
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (n : ℕ) :
    comparisonLE A (Nat.le_succ n) = comparison A n := sorry

/-- On an object represented before localization, the descended comparison is the source
comparison conjugated by the two canonical factorization isomorphisms. -/
theorem comparison_app_Q
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (n : ℕ) (M : System A) :
    (comparison A n).app ((Q A).obj M) =
      (Functor.isoWhiskerRight (evalFactors A (n + 1))
          (CochainDGAlgebra.Hom.Derived.extension
            (A.stepMap n))).hom.app M ≫
        (comparisonSource A n).app M ≫
          (evalFactors A n).inv.app M := sorry

/-- A global derived DG-module system is quasi-coherent when every adjacent extension comparison
is an isomorphism. -/
@[stacks 0GZ9 "quasi-coherent derived DG-module systems"]
def quasiCoherent (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :
    ObjectProperty (Category A) :=
  fun M ↦ ∀ n : ℕ, IsIso ((comparison A n).app M)

/-- Quasi-coherence is exactly invertibility of all adjacent extension comparisons. -/
theorem quasiCoherent_iff (M : Category A) :
    quasiCoherent A M ↔ ∀ n : ℕ, IsIso ((comparison A n).app M) := sorry

/-- A represented system is quasi-coherent exactly when all of its source-level adjacent
comparisons become isomorphisms. -/
theorem quasiCoherent_Q_iff (M : System A) :
    quasiCoherent A ((Q A).obj M) ↔
      ∀ n : ℕ, IsIso ((comparisonSource A n).app M) := sorry

/-- The category `QC(A)` of quasi-coherent objects in the global derived category `D(ℕ, A)`. -/
@[stacks 0GZ9 "quasi-coherent derived modules on a DGA inverse system"]
abbrev QC (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :=
  (quasiCoherent A).FullSubcategory

/-- Regard an ordinary DG-module system whose derived transition comparisons are invertible as
an object of `QC(A)`. -/
noncomputable def ofSystem (M : System A)
    (hM : ∀ n : ℕ, IsIso ((comparisonSource A n).app M)) : QC A :=
  ⟨(Q A).obj M, (quasiCoherent_Q_iff M).2 hM⟩

/-- The underlying global derived object of `ofSystem M hM` is represented by `M`. -/
@[simp]
theorem ofSystem_obj (M : System A)
    (hM : ∀ n : ℕ, IsIso ((comparisonSource A n).app M)) :
    (ofSystem M hM).obj = (Q A).obj M := sorry

/-- Every adjacent comparison of a quasi-coherent global derived module system is invertible. -/
instance comparisonIsIso (M : QC A) (n : ℕ) :
    IsIso ((comparison A n).app M.obj) := sorry

end DifferentialGradedModule.InverseSystem.Derived
