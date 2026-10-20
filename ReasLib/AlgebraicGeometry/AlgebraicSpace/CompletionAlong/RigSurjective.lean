module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective

/-!
# Rig-surjectivity of proper completion maps

A proper morphism into a locally Noetherian algebraic space that is surjective
over the complement of a closed subset induces a rig-surjective completion map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Completing the source of a proper morphism into a locally Noetherian
algebraic space along the closed preimage of `T` yields a locally Noetherian
formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong_preimage {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X) [Proper f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

/-- A proper morphism into a locally Noetherian algebraic space for which every
point outside a closed subset has a preimage induces a rig-surjective morphism
from the completion along its inverse image to the completion along that subset. -/
theorem rigSurjective_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [Proper f] (T : Closeds (Points X))
    (h_surj : ∀ x : Points X, x ∉ (T : Set (Points X)) →
      ∃ x' : Points X', Points.map f x' = x) :
    FormalAlgebraicSpace.RigSurjective (completionAlong.map f T) :=
  sorry

/-- For a separated locally of finite type morphism into a locally Noetherian
algebraic space, if the comparison of the open complements of a closed subset
and its inverse image is a monomorphism, the relative diagonal of the induced
morphism of formal completions is rig-surjective. -/
theorem rigSurjective_diagonal_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [Separated f] [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [Mono (openInverseImageTo f (OpenSubspace.Construction.ι X T.compl))] :
    FormalAlgebraicSpace.RigSurjective
      (pullback.diagonal (completionAlong.map f T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
