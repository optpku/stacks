module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Completion.Reduction
import StacksCheckRecall

/-!
# Reduction of the completion along a closed subspace

The reduction of the formal completion of an algebraic space along a closed
subspace is the reduction of that subspace.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 87.38.3: The reduction of the completion of an algebraic space along
a closed subspace is the reduction of that subspace, compatibly with their
embeddings into the ambient algebraic space. -/
@[stacks 0GXW] #check (AlgebraicGeometry.AlgebraicSpace.Completion.reduction_eq :
  ∀ {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u} (inclusion : Z ⟶ X)
    [AlgebraicSpace.IsAlgebraicSpace X] [AlgebraicSpace.IsAlgebraicSpace Z],
    Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion →
    (SpacePresheaf.reduction
      (AlgebraicGeometry.AlgebraicSpace.Completion.subfunctor inclusion).toFunctor).image
        (AlgebraicGeometry.AlgebraicSpace.Completion.subfunctor inclusion).ι =
      (SpacePresheaf.reduction Z).image inclusion)

/- The canonical morphism from the reduced subspace commutes with the ambient
inclusions. -/
#check (AlgebraicGeometry.AlgebraicSpace.Completion.fromReduction_comp_ι :
  ∀ {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u} (inclusion : Z ⟶ X)
    [AlgebraicSpace.IsAlgebraicSpace X] [AlgebraicSpace.IsAlgebraicSpace Z]
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion),
    AlgebraicGeometry.AlgebraicSpace.Completion.fromReduction inclusion hClosed ≫
      (AlgebraicGeometry.AlgebraicSpace.Completion.subfunctor inclusion).ι =
        (SpacePresheaf.reduction Z).ι ≫ inclusion)
