module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Situation 99.5.1: for a finite-presentation morphism `f : X ⟶ B`, the category
of triples `(T, g, F)` has `T` a scheme over `S`, `g : T ⟶ B` over `S`, and `F`
a finitely presented quasi-coherent module on `X_T`, flat over `T` with support
proper over `T`. Morphisms are maps of schemes over `B` together with
isomorphisms from the pulled-back target module to the source module. -/
@[stacks 08KB] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.category :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    [FinitePresentation f] → CategoryTheory.Cat.{u + 1, u + 1})
