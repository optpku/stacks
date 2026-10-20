module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.ClosedImmersion
import StacksCheckRecall

/-!
# Closed immersions of completions

If a morphism of algebraic spaces is a closed immersion, then the induced
morphism of formal completions along a closed subset is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

/- Lemma 88.23.3: If `f : X' ⟶ X` is a closed immersion, then the induced
morphism `completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is a closed immersion of formal algebraic spaces. -/
@[stacks 0GDC] #check
  (AlgebraicGeometry.AlgebraicSpace.closedImmersion_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicSpace.IsClosedImmersion f] (T : Closeds (Points X)),
      FormalAlgebraicSpace.ClosedImmersion (completionAlong.map f T))
