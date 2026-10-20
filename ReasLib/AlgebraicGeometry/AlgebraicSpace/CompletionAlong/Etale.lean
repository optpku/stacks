module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale

/-!
# Étale morphisms of completions

An étale morphism of algebraic spaces induces an étale morphism of formal
completions along a closed subset and its inverse image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `f : X' ⟶ X` is étale, then the induced morphism from the completion of
`X'` along the inverse image of a closed subset `T` of `Points X` to the
completion of `X` along `T` is étale. -/
instance etale_completionAlongMap {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) [AlgebraicSpace.Etale f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.Etale (completionAlong.map f T) :=
  sorry

namespace completionAlong

/-- A locally finite-type morphism to a locally Noetherian algebraic space
that is an isomorphism over the complement of a closed subset is étale if and
only if its induced morphism of completions is étale. -/
theorem etale_iff_map {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [LocallyOfFiniteType f] [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.Etale f ↔ FormalAlgebraicSpace.Etale (map f T) :=
  sorry

/-- A locally finite-type morphism to a locally Noetherian algebraic space
that is an isomorphism away from a closed subset is étale if and only if a
corresponding rig-étale morphism from a locally Noetherian formal algebraic
space to the completion is étale. Correspondence is an isomorphism from the
completion of the source over the completed target. -/
theorem etale_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [LocallyOfFiniteType f] [IsIso (openInverseImageTo f (openComplementι X T))]
    {W : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsLocallyNoetherian W] (g : W ⟶ completionAlong X T)
    [FormalAlgebraicSpace.RigEtale g]
    (e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W)
    (he : e.hom ≫ g = map f T) :
    AlgebraicSpace.Etale f ↔ FormalAlgebraicSpace.Etale g :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
