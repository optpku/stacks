module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 42.33.2: flat pullback along a flat morphism of relative dimension `r`
defines a bivariant class of degree `-r`. -/
@[stacks 0B78] #check (AlgebraicGeometry.BivariantClass.flatPullback :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r],
    BivariantClass δ f (-(r : ℤ)))
