module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineSpace
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Example 67.53.3 (5): the map `X ⟶ 𝔸¹_k` is a universal homeomorphism. -/
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.universalHomeomorphism_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      AlgebraicGeometry.AlgebraicSpace.Sheaf.isUniversalHomeomorphism (toAffineLine k))

/- Example 67.53.3 (1): the first arrow `𝔸¹_k ⟶ X` is étale surjective. -/
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.etale_atlas :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom)
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.locallySurjective_atlas :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom)

/- Example 67.53.3 (2): the second arrow `X ⟶ 𝔸¹_k` is universally injective. -/
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.universallyInjective_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
        (Limits.pullback.diagonal (toAffineLine k)).hom)

/- Example 67.53.3 (3): the composition is the map `x ↦ x²`. -/
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.toAffineLine_comp_atlas :
    ∀ (k : Type u) [Field k],
      atlas k ≫ toAffineLine k =
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (squareOver k))

/- Example 67.53.3 (4): the composition is universally closed. -/
@[stacks 05Z6] #check
  (AlgebraicGeometry.AffineSpace.squareMap_universallyClosed :
    ∀ (k : Type u) [Field k], UniversallyClosed (squareMap k))
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.universallyClosed_comp_atlas_toAffineLine :
    ∀ (k : Type u) [Field k],
      (MorphismProperty.over (@UniversallyClosed)).relative uliftYoneda.{u + 1}
        (atlas k ≫ toAffineLine k).hom)

/- Example 67.53.3 (6): the map `X ⟶ 𝔸¹_k` is not separated. -/
@[stacks 05Z6] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.not_separated_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      ¬ (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
          (Limits.pullback.diagonal (toAffineLine k)).hom)
