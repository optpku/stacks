module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.24.5: if `g ∘ f` is locally of finite type then so is `f`. -/
@[stacks 0AQ6] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType (f ≫ g)],
      LocallyOfFiniteType f)
