module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigEtale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification

/-!
# Formal modifications from completed proper morphisms

A proper morphism of algebraic spaces into a locally Noetherian target that is
an isomorphism off a closed subset induces a formal modification of completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism into a locally Noetherian algebraic space that is an
isomorphism over the complement of a closed subset induces a formal modification
from the completion along its inverse image to the completion along that subset. -/
instance formalModification_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [AlgebraicSpace.Proper f] (T : Closeds (Points X))
    [IsIso (Open.complementComparison f T)] :
    FormalAlgebraicSpace.FormalModification (completionAlong.map f T) :=
  sorry

/-- A locally finite-type morphism into a locally Noetherian algebraic space
that is an isomorphism over the complement of a closed subset is proper if and
only if its canonical map of completions along that subset is a formal
modification. -/
@[stacks 0ARX]
theorem completionFunctor.proper_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.Proper f ↔
      FormalAlgebraicSpace.FormalModification (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
