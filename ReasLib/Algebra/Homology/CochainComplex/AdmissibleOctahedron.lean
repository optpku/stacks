/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Admissible
public import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.Octahedron
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Octahedra from admissible cochain maps

This leaf connects admissibility for the graded-forgetful functor to the reusable
degreewise-split quotient-row construction in the homotopy category.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated ComplexShape
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Admissibly monic cochain maps admit degreewise-split quotient rows whose distinguished
triangles form an octahedron. -/
@[stacks 09KI "admissible cochain maps determine an octahedron"]
theorem nonemptyOctahedron_of_admissibleMono {K L M : CochainComplex C ℤ}
    (α : K ⟶ L) (β : L ⟶ M)
    (hα : IsAdmissibleMono (forgetToGraded C) α)
    (hβ : IsAdmissibleMono (forgetToGraded C) β) :
    ∃ (S₁₂ : DegreewiseSplitQuotient α)
      (S₁₃ : DegreewiseSplitQuotient (α ≫ β))
      (S₂₃ : DegreewiseSplitQuotient β)
      (d₁₂ : S₁₂.triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (d₂₃ : S₂₃.triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (d₁₃ : S₁₃.triangle ∈ distTriang (HomotopyCategory C (up ℤ))),
      Nonempty (Octahedron
        (Functor.map_comp (HomotopyCategory.quotient C (up ℤ)) α β).symm
          d₁₂ d₂₃ d₁₃) := sorry

end CochainComplex
