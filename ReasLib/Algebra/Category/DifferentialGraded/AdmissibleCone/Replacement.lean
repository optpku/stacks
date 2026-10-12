/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Factorization
public import ReasLib.CategoryTheory.ComposableArrows.Property
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite admissibly monic homotopy replacements

Finite rows in `Comp` admit a comparison row with admissibly monic successor maps and
componentwise homotopy equivalences.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DifferentialGradedCategory.Comp.HomotopyReplacement

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasBinaryBiproducts (Comp R A)]

/-- A finite row has an admissibly monic replacement with displayed homotopy-retract
comparisons. -/
theorem exists_withRetracts (C : B.AdmissibleCones)
    {n : ℕ} (X : ComposableArrows (Comp R A) n) :
    ∃ (Y : ComposableArrows (Comp R A) n) (ι : Y ⟶ X)
      (r : ∀ i : Fin (n + 1), HomotopyRetract (Y.obj i) (X.obj i)),
      ComposableArrows.arrowProperty Comp.admissibleMonomorphisms Y ∧
        ∀ i : Fin (n + 1), (r i).projection = ι.app i := sorry

/-- Lemma 22.27.7 (09QN): every finite row has an admissibly monic replacement whose
comparison is componentwise a homotopy equivalence. -/
@[stacks 09QN]
theorem exists_admissibleMono (C : B.AdmissibleCones)
    {n : ℕ} (X : ComposableArrows (Comp R A) n) :
    ∃ (Y : ComposableArrows (Comp R A) n) (ι : Y ⟶ X),
      ComposableArrows.arrowProperty Comp.admissibleMonomorphisms Y ∧
        ComposableArrows.componentProperty Comp.homotopyEquivalences ι := sorry

end DifferentialGradedCategory.Comp.HomotopyReplacement
