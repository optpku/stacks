module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Union
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-!
# Finite covers of quasi-compact open substacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicStack.Substack

/-- A quasi-compact open substack contained in a union of open substacks is
contained in the union of a finite subfamily. -/
theorem exists_finset_iUnion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [IsQuasiCompact Y]
    (j : Y ⟶ X) [Groupoids.Hom.OpenImmersion j] {I : Type v}
    (P : I → ObjectProperty X.total) (hP : ∀ i, Substack.IsOpen X (P i)) :
    (CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor j).essImage ≤
        Substack.iUnion P →
      ∃ t : Finset I,
        (CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor j).essImage ≤
          Substack.iUnion (fun i : t ↦ P i) := sorry

end AlgebraicGeometry.AlgebraicStack.Substack
