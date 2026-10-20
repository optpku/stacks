module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.BaseLocus
import StacksCheckRecall

/-!
# Where a morphism of algebraic spaces is a closed immersion

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite type and universally closed, and with `Y ⟶ Z`
separated, a test map into `Z` factors through the closed-immersion base
locus if and only if the base-changed map `X_{Z'} ⟶ Y_{Z'}` is a closed
immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion

/- Lemma 76.49.3: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite type and universally closed, and that `q` is separated. Then a
morphism `g : Z' ⟶ Z` factors through the open subspace
`baseLocus f q ⊂ Z` if and only if the base change
`Unramified.overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is a closed immersion. -/
@[stacks 05XA] #check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.exists_lift_iff_overBaseChange :
    ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q],
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      IsClosedImmersion (Unramified.overBaseChange f q g))

end AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
