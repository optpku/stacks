module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 32.14.2 (1): for a quasi-compact morphism of schemes, universal closedness is
equivalent to closedness of every base change by a morphism locally of finite presentation. -/
@[stacks 05JX] #check
  (AlgebraicGeometry.UniversallyClosed.iff_isClosedMap_baseChange_of_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f],
      UniversallyClosed f ↔
        ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFinitePresentation g →
          IsClosedMap (pullback.snd f g).base)

/- Lemma 32.14.2 (2): for a quasi-compact morphism of schemes, universal closedness is
equivalent to closedness after base change along every relative affine-space projection
`AffineSpace (ULift.{u} (Fin n)) S ↘ S`. -/
@[stacks 05JX] #check
  (AlgebraicGeometry.UniversallyClosed.iff_isClosedMap_affineSpace_baseChange :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f],
      UniversallyClosed f ↔
        ∀ n : ℕ,
          IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base)
