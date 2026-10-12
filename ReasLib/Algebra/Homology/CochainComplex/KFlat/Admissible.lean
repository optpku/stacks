/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Triangulated
public import ReasLib.Algebra.Homology.HomologicalComplex.Admissible
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.TermwiseFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Admissible extensions of K-flat termwise-flat complexes

An admissible short exact sequence is split after forgetting the differential.  The split graded
sequence controls termwise flatness, while its associated distinguished triangle controls
K-flatness.  This file combines those two reusable closure mechanisms.
@stack 06Y2
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex.KFlat.termwiseFlat

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- In an admissible short exact sequence of cochain complexes, K-flat termwise-flatness of the
first two terms implies it for the third. -/
@[stacks 06Y2 "degreewise-split companion, third term"]
theorem obj₃_of_admissible (S : ShortComplex (CochainComplex C ℤ))
    (hS : IsAdmissibleShortExact (HomologicalComplex.forget C (up ℤ)) S)
    (h₁ : HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₁)
    (h₂ : HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₂) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₃ := sorry

/-- In an admissible short exact sequence of cochain complexes, K-flat termwise-flatness of the
outer terms implies it for the middle term. -/
@[stacks 06Y2 "degreewise-split companion, middle term"]
theorem obj₂_of_admissible (S : ShortComplex (CochainComplex C ℤ))
    (hS : IsAdmissibleShortExact (HomologicalComplex.forget C (up ℤ)) S)
    (h₁ : HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₁)
    (h₃ : HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₃) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₂ := sorry

/-- In an admissible short exact sequence of cochain complexes, K-flat termwise-flatness of the
last two terms implies it for the first. -/
@[stacks 06Y2 "degreewise-split companion, first term"]
theorem obj₁_of_admissible (S : ShortComplex (CochainComplex C ℤ))
    (hS : IsAdmissibleShortExact (HomologicalComplex.forget C (up ℤ)) S)
    (h₂ : HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₂)
    (h₃ : HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₃) :
    HomologicalComplex.KFlat.termwiseFlat (up ℤ) S.X₁ := sorry

end HomologicalComplex.KFlat.termwiseFlat
