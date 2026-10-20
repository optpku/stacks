module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ArtinNoetherian

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

universe u

/- Proposition 98.26.1: a presheaf satisfying the Noetherian Artin axioms extends
uniquely, up to natural isomorphism, to an algebraic space. -/
@[stacks 0GE7] #check
  (AlgebraicGeometry.AlgebraicSpace.existsUnique_of_noetherianArtinAxioms :
    ∀ {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (hΔ : uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag F))
    (h_size : Noetherian.boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S) F)
    (h1 : Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F)
    [HasRimSchlessinger F] [HasFiniteDimensionalTangentSpaces F]
    [HasEffectiveFormalObjects F] [OpennessOfVersality F]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    ∃ X : AlgebraicSpace S,
      Nonempty ((restrictPresheaf S).obj
        (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj X).obj ≅ F) ∧
        ∀ Y : AlgebraicSpace S,
          Nonempty ((restrictPresheaf S).obj
            (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj Y).obj ≅ F) →
            Nonempty ((AlgebraicGeometry.AlgebraicSpace.toSheaf.obj X).obj ≅
              (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj Y).obj))
