module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.EtaleFactorization
import StacksCheckRecall

/-!
# Algebraization of morphisms of completions along a closed subset

A morphism of completions along `T` over a Noetherian affine algebraic space,
coming from a locally finite-type morphism étale off `T`, algebraizes after an
étale localization of the source that is an isomorphism on completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/- Lemma 88.25.2: A morphism of completions into a locally finite-type space
étale off the closed subset algebraizes after an affine étale localization
inducing an isomorphism on completions. -/
@[stacks 0AR3] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.exists_etaleFactor :
  ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsAffine X] [IsAffine X'] [IsAffine Y]
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y]
    (T : Closeds (Points X)) (f : X' ⟶ X) [LocallyOfFiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T))) (h : Y ⟶ X)
    (α : completionAlong Y (T.preimage (Points.continuous_map h)) ⟶
      completionAlong X' (T.preimage (Points.continuous_map f)))
    (hα : α ≫ map f T = map h T),
    ∃ (Y' : AlgebraicSpace S) (_ : IsAffine Y') (b : Y' ⟶ Y) (_ : Etale b)
      (a : Y' ⟶ X') (h_over : a ≫ f = b ≫ h)
      (_ : IsIso (mapOverHom T h (b ≫ h) b rfl)),
      α = inv (mapOverHom T h (b ≫ h) b rfl) ≫
        mapOverHom T f (b ≫ h) a h_over)

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
