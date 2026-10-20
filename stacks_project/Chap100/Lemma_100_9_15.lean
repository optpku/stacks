module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.QuasiCompact
import StacksCheckRecall

/-!
# Finite subcover of a quasi-compact open substack

A quasi-compact open substack contained in a union of open substacks is
already contained in the union of a finite subfamily.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

/- Lemma 100.9.15: A quasi-compact open substack covered by a family of open
substacks is covered by a finite subfamily. -/
@[stacks 05UR] #check
  (AlgebraicGeometry.AlgebraicStack.Substack.exists_finset_iUnion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y]
      [AlgebraicGeometry.AlgebraicStack.IsQuasiCompact Y]
      (j : Y ⟶ X) [Groupoids.Hom.OpenImmersion j] {I : Type v}
      (P : I → ObjectProperty X.total)
      (hP : ∀ i, AlgebraicGeometry.AlgebraicStack.Substack.IsOpen X (P i)),
      (CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor j).essImage ≤
          AlgebraicGeometry.AlgebraicStack.Substack.iUnion P →
        ∃ t : Finset I,
          (CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor j).essImage ≤
            AlgebraicGeometry.AlgebraicStack.Substack.iUnion (fun i : t ↦ P i))

