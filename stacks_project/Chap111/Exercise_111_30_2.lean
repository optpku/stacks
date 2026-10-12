/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Lifting
import StacksCheckRecall

@[expose] public section

universe v u

/- Exercise 111.30.2 -/
@[stacks 0289]
#check
  (CategoryTheory.FilteredObject.injective_gradedPiece_iff_factors :
    ∀ {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
      {I : CategoryTheory.FilteredObject C}
      (hI : CategoryTheory.IndexedFiltration.IsFinite I.filtration),
      (∀ p : ℤ, CategoryTheory.Injective (I.gradedPiece p)) ↔
        ∀ {A B : CategoryTheory.FilteredObject C}
          (hA : CategoryTheory.IndexedFiltration.IsFinite A.filtration)
          (hB : CategoryTheory.IndexedFiltration.IsFinite B.filtration)
          (α : CategoryTheory.FilteredObject.Hom A B)
          (f : CategoryTheory.FilteredObject.Hom A I),
          (∀ p : ℤ,
            CategoryTheory.Mono (CategoryTheory.Limits.cokernel.map (A.filtration.succInclusion p)
              (B.filtration.succInclusion p) (α.stageMap (p + 1)) (α.stageMap p)
              (CategoryTheory.FilteredObject.Hom.succInclusion_naturality α p))) →
            ∃ g : CategoryTheory.FilteredObject.Hom B I,
              CategoryTheory.FilteredObject.Hom.comp α g = f)
