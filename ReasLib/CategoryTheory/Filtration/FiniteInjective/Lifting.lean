/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Morphism
public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Finite Graded-Injectivity Lifting

For finite filtrations, injectivity of every graded piece is equivalent to the
extension property for morphisms whose graded-piece maps are monomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace FilteredObject

/-- For a finite filtration, graded-piece injectivity is equivalent to the corresponding lifting
property for filtered morphisms with monomorphic graded-piece maps. -/
theorem injective_gradedPiece_iff_factors {C : Type u} [Category.{v} C] [Abelian C]
    {I : FilteredObject C} (hI : IndexedFiltration.IsFinite I.filtration) :
    (∀ p : ℤ, Injective (I.gradedPiece p)) ↔
      ∀ {A B : FilteredObject C} (hA : IndexedFiltration.IsFinite A.filtration)
        (hB : IndexedFiltration.IsFinite B.filtration) (α : FilteredObject.Hom A B)
        (f : FilteredObject.Hom A I),
        (∀ p : ℤ,
          Mono (Limits.cokernel.map (A.filtration.succInclusion p)
            (B.filtration.succInclusion p) (α.stageMap (p + 1)) (α.stageMap p)
            (FilteredObject.Hom.succInclusion_naturality α p))) →
          ∃ g : FilteredObject.Hom B I, FilteredObject.Hom.comp α g = f := sorry

end FilteredObject

end CategoryTheory
