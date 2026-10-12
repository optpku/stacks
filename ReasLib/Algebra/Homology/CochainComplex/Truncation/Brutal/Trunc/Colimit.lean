/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Canonical Colimit of the Brutal Truncation Diagram

The canonical cocone from the brutal truncation diagram to its source complex
is a colimit cocone.  The universal map is defined degreewise from an explicit
stage at which that degree has stabilized; only its universal-property laws
are deferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A canonical brutal-truncation stage which contains degree `i`. -/
@[stacks 0D8Z]
abbrev stageForDegree (i : ℤ) : ℕ :=
  Int.toNat (-i)

/-- The cutoff of `stageForDegree i` is at most `i`. -/
@[stacks 0D8Z]
theorem index_stageForDegree_le (i : ℤ) :
    Brutal.Tower.index (stageForDegree i) ≤ i := sorry

/-- At any retained degree, evaluation of the brutal diagram is canonically
isomorphic to evaluation of the original complex. -/
@[stacks 0D8Z]
noncomputable def degreeIso (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : Brutal.Tower.index n ≤ i) :
    ((diagram K).obj n).X i ≅ K.X i :=
  eqToIso (congrArg (fun L : CochainComplex A ℤ ↦ L.X i) (diagram_obj K n)) ≪≫
    StupidTrunc.activeIso K (Brutal.Tower.index n) i hi

namespace Evaluation

/-- The explicit factorization from the stabilized value `K.X i` through an
arbitrary cocone of the degree-`i` evaluation diagram. -/
@[stacks 0D8Z]
noncomputable def desc (K : CochainComplex A ℤ) (i : ℤ)
    (s : Cocone (diagram K ⋙ HomologicalComplex.eval A (up ℤ) i)) :
    K.X i ⟶ s.pt :=
  (degreeIso K (stageForDegree i) i (index_stageForDegree_le i)).inv ≫
    s.ι.app (stageForDegree i)

/-- Degreewise evaluation of the canonical brutal-truncation cocone is a
colimit cocone. -/
@[stacks 0D8Z]
noncomputable def isColimit (K : CochainComplex A ℤ) (i : ℤ) :
    IsColimit ((HomologicalComplex.eval A (up ℤ) i).mapCocone (cocone K)) where
  desc := desc K i
  fac := sorry
  uniq := sorry

end Evaluation

/-- The canonical cocone from the brutal truncation diagram to the original
complex satisfies the colimit universal property. -/
@[stacks 0D8Z]
noncomputable def isColimit (K : CochainComplex A ℤ) : IsColimit (cocone K) :=
  HomologicalComplex.isColimitOfEval (diagram K) (cocone K)
    (Evaluation.isColimit K)

/-- The brutal truncation diagram equipped with its canonical colimit
universal property. -/
@[stacks 0D8Z]
noncomputable def colimitCocone (K : CochainComplex A ℤ) :
    ColimitCocone (diagram K) :=
  ⟨cocone K, isColimit K⟩

end CategoryTheory.CochainComplex.Brutal.Trunc
