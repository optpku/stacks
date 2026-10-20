module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Étale algebraization of morphisms of completions

Morphisms of completions into a locally finite-type space étale away from the
closed subset algebraize after an affine étale localization of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- For Noetherian affine algebraic spaces `X`, `X'`, and `Y`, a morphism of
completions over `X` into the completion of a locally finite-type morphism
`f : X' ⟶ X` étale outside a closed subset `T` algebraizes after an affine
étale localization `b : Y' ⟶ Y` inducing an isomorphism on completions:
`α = a_/T ∘ b_/T⁻¹` for a morphism `a : Y' ⟶ X'` over `X`. -/
@[stacks 0AR3]
theorem exists_etaleFactor {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsAffine X] [IsAffine X'] [IsAffine Y]
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y]
    (T : Closeds (Points X)) (f : X' ⟶ X) [LocallyOfFiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T))) (h : Y ⟶ X)
    (α : completionAlong Y (T.preimage (Points.continuous_map h)) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)))
    (hα : α ≫ map f T = map h T) :
    ∃ (Y' : AlgebraicSpace S) (_ : IsAffine Y') (b : Y' ⟶ Y) (_ : Etale b)
      (a : Y' ⟶ X') (h_over : a ≫ f = b ≫ h)
      (_ : IsIso (mapOverHom T h (b ≫ h) b rfl)),
      α = inv (mapOverHom T h (b ≫ h) b rfl) ≫
        mapOverHom T f (b ≫ h) a h_over :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
