module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.CartierGysin

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Lemma 42.35.2: a Chow-level cap family satisfying proper-pushforward,
flat-pullback, and trivial-restriction Cartier-Gysin compatibility determines a
degree-`p` bivariant class. -/
@[stacks 0F9A] #check
  (AlgebraicGeometry.BivariantClass.ofTrivialCartierGysin :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (delta : S → ℤ) [IsDimensionFunction delta]
      {X Y : Over S} (f : X ⟶ Y)
      [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (p : ℤ) (cap : CapFamily delta f p),
      CompatibleWithProperPushforward delta cap →
        CompatibleWithFlatPullback delta cap →
          CompatibleWithTrivialCartierGysinOnChow delta cap →
            AlgebraicGeometry.BivariantClass delta f p)

end AlgebraicGeometry.BivariantClass
