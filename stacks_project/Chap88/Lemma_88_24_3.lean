module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FormalModification
import StacksCheckRecall

/-!
# Formal modifications from completed proper morphisms

In the Section 88.23 completion-functor setup, a proper morphism of algebraic
spaces that is an isomorphism off a closed subset induces a formal modification
of formal completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

/- Lemma 88.24.3: in the Section 88.23 setup, with `U` the open complement of
the closed subset `T ⊆ Points X`, `T'` the closed preimage of `T` along `f`,
and `U'` the inverse image of `U`, if `X` is locally Noetherian, `f` is proper,
and the comparison `openInverseImageTo f (OpenSubspace.ofOpensι T.compl)` is an
isomorphism, then `completionAlong.map f T` is a formal modification. -/
@[stacks 0GDM] #check
  (AlgebraicGeometry.AlgebraicSpace.formalModification_completionAlongMap :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [AlgebraicSpace.Proper f] (T : Closeds (Points X))
    [IsIso (Open.complementComparison f T)],
    FormalAlgebraicSpace.FormalModification (completionAlong.map f T))
