/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.TwoStep
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of Two-Step Quotient Boundaries

This leaf module specializes the existing homology-sequence naturality theorem to the canonical
two-step quotient sequence of a filtered homological complex.  The construction of the quotient
sequence itself stays in the lighter `TwoStep` owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace CategoryTheory
namespace HomologicalComplex.Filtered.TwoStep

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- The connecting morphism of the canonical two-step quotient sequence is natural in a
filtered-complex morphism. -/
@[reassoc, stacks 012D "naturality of the two-step quotient boundary"]
theorem boundary_naturality {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) {i j : ι} (hij : c.Rel i j) :
    boundary K p hij ≫ HomologicalComplex.homologyMap (gradedPieceMap f (p + 1)) j =
      HomologicalComplex.homologyMap (gradedPieceMap f p) i ≫ boundary L p hij := sorry

end HomologicalComplex.Filtered.TwoStep
end CategoryTheory
