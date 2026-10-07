module

public import stacks_project.Chap73.Lemma_73_8_3_PhCovering
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 73.8.3: Let `S` be a scheme. Let `f : Y ⟶ X` be a surjective proper morphism of
algebraic spaces over `S`. Then `{Y ⟶ X}` is a ph covering. -/
@[stacks 0DFI] #check
  (@AlgebraicGeometry.AlgebraicSpace.phCoveringSingletonOfProperSurjective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.Proper f]
      [AlgebraicGeometry.AlgebraicSpace.Surjective f],
      AlgebraicGeometry.AlgebraicSpace.PhCovering
        (fun _ : PUnit ↦ Y) (fun _ ↦ f))
