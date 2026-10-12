/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Objects Used by Extension Spectral Sequences

This file provides the two elementary derived-category objects used to state the pages of
extension spectral sequences.  It is deliberately independent of filtered complexes.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedExt

noncomputable section

universe t v u

namespace CategoryTheory.DerivedCategory.Ext

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

/-- The degree-`j` cohomology object of `K`, placed in cochain degree zero in the derived
category. -/
abbrev cohomologyObject (K : DerivedCategory A) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj
    ((DerivedCategory.homologyFunctor A j).obj K)

/-- The degree-`j` term of a cochain complex, placed in cochain degree zero in the derived
category. -/
abbrev termObject (K : CochainComplex A ℤ) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj (K.X j)

end Derived

end CategoryTheory.DerivedCategory.Ext
