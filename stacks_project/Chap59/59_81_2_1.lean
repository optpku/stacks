module

public import ReasLib.AlgebraicGeometry.GroupSchemePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open AlgebraicGeometry.GroupScheme
open scoped AlgebraicGeometry CategoryTheory.MonObj

/- 59.81.2.1: the short exact sequence 0 ⟶ underline(Z / ℓ Z)_A ⟶ G ⟶ H ⟶ 0
has the constant group scheme as the kernel of its presentation morphism. -/
@[stacks 0GY4] #check
  (AlgebraicGeometry.GroupScheme.presentation_isKernel :
    ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : Nat.Prime ℓ),
    (constantIncl ℓ ≫ presentationHom ℓ).hom.hom =
        toUnit (constantZModGroupScheme ℓ).X ≫ η[(presentationH ℓ).X] ∧
      ∀ {T : Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ)))}
        (g : T ⟶ (presentationG ℓ).X),
        g ≫ (presentationHom ℓ).hom.hom =
            toUnit T ≫ η[(presentationH ℓ).X] →
          ∃! k : T ⟶ (constantZModGroupScheme ℓ).X,
            k ≫ (constantIncl ℓ).hom.hom = g)

/- The presentation morphism is faithfully flat, giving the surjectivity clause. -/
#check
  (AlgebraicGeometry.GroupScheme.presentationHom_faithfullyFlat :
    ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : Nat.Prime ℓ),
    (Localization.Away.PolynomialPresentation.baseMap (presentationPi ℓ) ℓ (presentationPhi ℓ)
        (presentationPhi_shape ℓ)).toRingHom.FaithfullyFlat)
