module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Etale
import StacksCheckRecall

/-!
# Étale morphisms correspond under completion

In the standing locally Noetherian setup of Theorem 88.27.4, a morphism
`f : X' ⟶ X` is étale if and only if the corresponding morphism of
completions `g : W ⟶ X_/T` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/- Lemma 88.28.5: with assumptions and notation as in Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ completionAlong X T`, then `f` is étale
if and only if `g` is étale. Correspondence is an isomorphism
`e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W` with
`e.hom ≫ g = map f T`. -/
@[stacks 0GI4] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.etale_iff :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [LocallyOfFiniteType f] [IsIso (openInverseImageTo f (openComplementι X T))]
    {W : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsLocallyNoetherian W] (g : W ⟶ completionAlong X T)
    [FormalAlgebraicSpace.RigEtale g]
    (e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W)
    (he : e.hom ≫ g = map f T),
    AlgebraicSpace.Etale f ↔ FormalAlgebraicSpace.Etale g)

/- In the standing locally Noetherian setup of Theorem 88.27.4, a locally
finite-type morphism `f : X' ⟶ X` that is an isomorphism over the open
complement of `T` is étale if and only if `map f T` is étale. -/
#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.etale_iff_map :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [LocallyOfFiniteType f] [IsIso (openInverseImageTo f (openComplementι X T))],
    AlgebraicSpace.Etale f ↔ FormalAlgebraicSpace.Etale (map f T))

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
