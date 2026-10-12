/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.PageTower

/-!
# Naturality of Page-Cycle and Page-Boundary Maps

The page-cycle and page-boundary restrictions are functorial in a homology-page-tower morphism.
Their identity and composition laws are kept in this small leaf, matching the corresponding API
already available for local homology, recursive cycles, recursive boundaries, and page quotients.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologyPageTower

variable {P Q R : HomologyPageTower C}

namespace PageCycle

/-- Restricting the identity tower morphism to page cycles gives the identity. -/
@[simp, stacks 011O "identity on page-cycle maps"]
theorem map_id (P : HomologyPageTower C) (r : ℕ+) :
    map (𝟙 P) r = 𝟙 (P.pageCycle r : C) := sorry

/-- Page-cycle restriction preserves composition of tower morphisms. -/
@[simp, stacks 011O "composition of page-cycle maps"]
theorem map_comp (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    map (f ≫ g) r = map f r ≫ map g r := sorry

end PageCycle

namespace PageBoundary

/-- Restricting the identity tower morphism to page boundaries gives the identity. -/
@[simp, stacks 011O "identity on page-boundary maps"]
theorem map_id (P : HomologyPageTower C) (r : ℕ+) :
    map (𝟙 P) r = 𝟙 (P.pageBoundary r : C) := sorry

/-- Page-boundary restriction preserves composition of tower morphisms. -/
@[simp, stacks 011O "composition of page-boundary maps"]
theorem map_comp (f : P ⟶ Q) (g : Q ⟶ R) (r : ℕ+) :
    map (f ≫ g) r = map f r ≫ map g r := sorry

end PageBoundary

end HomologyPageTower

end CategoryTheory
