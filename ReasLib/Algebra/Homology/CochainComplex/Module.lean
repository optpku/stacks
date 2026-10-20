module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Single

/-!
# Differential graded modules as cochain complexes

This leaf records the standard cochain-complex and homotopy-category models
for differential graded modules over an ordinary ring.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace ModuleCat

/-- Differential graded modules over `A`, modeled as cochain complexes of `A`-modules. -/
abbrev DGMod (A : Type u) [Ring A] := CochainComplex (ModuleCat A) ℤ

/-- The homotopy category of differential graded modules over `A`. -/
abbrev KDGMod (A : Type u) [Ring A] := HomotopyCategory (ModuleCat A) (up ℤ)

end ModuleCat

namespace CochainComplex

/-- The shifted free differential graded module `A[k]` in the canonical cochain-complex model. -/
abbrev shiftedFreeDGModule (A : Type u) [Ring A] (k : ℤ) :
    CochainComplex (ModuleCat.{u, u} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u, u} A) (ComplexShape.up ℤ) (-k)).obj
    (ModuleCat.of.{u, u} A A)

/-- The shifted free differential graded module is the single complex on `A` in degree `-k`. -/
@[simp]
theorem shiftedFreeDGModule_def (A : Type u) [Ring A] (k : ℤ) :
    shiftedFreeDGModule A k =
      (HomologicalComplex.single (ModuleCat.{u, u} A) (ComplexShape.up ℤ) (-k)).obj
        (ModuleCat.of.{u, u} A A) := sorry

end CochainComplex
