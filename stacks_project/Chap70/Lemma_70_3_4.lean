module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Cancellation
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry

universe u v

/- Lemma 70.3.4: Let `S` be a scheme and let `F`, `G`, `H : (Over S)ᵒᵖ ⥤ Type v`.
Let `a : F ⟶ G` and `b : G ⟶ H` be transformations of functors. If the composite
`a ≫ b : F ⟶ H` (Stacks `b ∘ a`) and `b` are limit preserving, then `a` is limit
preserving. -/
@[stacks 0GDY] #check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving.of_comp :
    ∀ {S : Scheme.{u}} {F G H : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v}
      {a : F ⟶ G} {b : G ⟶ H},
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving (a ≫ b) →
        AlgebraicGeometry.Scheme.Over.IsLimitPreserving b →
          AlgebraicGeometry.Scheme.Over.IsLimitPreserving a)
