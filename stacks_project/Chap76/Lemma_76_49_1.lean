module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.BaseLocus
import StacksCheckRecall

/-!
# Where a morphism of algebraic spaces is unramified

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite type and closed, a test map into `Z` factors
through the unramified base locus if and only if the base-changed map
`X_{Z'} ⟶ Y_{Z'}` is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 76.49.1: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite type and closed. Then a morphism `g : Z' ⟶ Z` factors through the open
subspace `baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is unramified. -/
@[stacks 05X8] #check (AlgebraicGeometry.AlgebraicSpace.Unramified.exists_lift_iff_overBaseChange :
    ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
      [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)],
      (∃ ℓ : Z' ⟶ (Unramified.baseLocus f q).X,
        ℓ ≫ (Unramified.baseLocus f q).ι = g) ↔
        Unramified (Unramified.overBaseChange f q g))
