module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry

universe u v

/- Lemma 70.3.3: Let `S` be a scheme and let `F`, `G`, `H : (Over S)ᵒᵖ ⥤ Type v`.
Let `a : F ⟶ G` and `b : G ⟶ H` be transformations of functors. If `a` and `b`
are limit preserving, then the composite `a ≫ b : F ⟶ H` (Stacks `b ∘ a`) is
limit preserving. -/
@[stacks 049L] #check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving.comp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
      {a : F ⟶ G} {b : G ⟶ H},
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving a →
        AlgebraicGeometry.Scheme.Over.IsLimitPreserving b →
          AlgebraicGeometry.Scheme.Over.IsLimitPreserving (a ≫ b))
