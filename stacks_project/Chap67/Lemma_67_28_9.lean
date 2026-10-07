module

public import stacks_project.Chap67.Lemma_67_28_9_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.28.9: if `X` is locally of finite presentation over `Z` and `Y` is
locally of finite type over `Z`, then `f : X ⟶ Y` is locally of finite
presentation. -/
@[stacks 05WT] #check
  (LocallyOfFinitePresentation.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g],
      LocallyOfFinitePresentation f)
