module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigSmooth
import StacksCheckRecall

/-!
# Rig-smooth morphisms of completions

If a locally of finite type morphism into a locally Noetherian algebraic space
is smooth over the complement of a closed subset, then the induced morphism of
formal completions is rig-smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

universe u

/- Lemma 88.23.8: if `X` is locally Noetherian, `f : X' ⟶ X` is locally of
finite type, and the comparison of the open complements of `T` is smooth, then
`completionAlong.map f T` is rig-smooth. -/
@[stacks 0GDH] #check (AlgebraicGeometry.AlgebraicSpace.rigSmooth_completionAlongMap :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [AlgebraicSpace.Smooth (Open.complementComparison f T)],
    FormalAlgebraicSpace.RigSmooth (completionAlong.map f T))
