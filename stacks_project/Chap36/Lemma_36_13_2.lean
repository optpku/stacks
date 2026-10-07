module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory ExactFunctor.Derived.Bounded

universe u w

/- Lemma 36.13.2: bounded derived restriction of coherent modules along an open immersion
into a Noetherian scheme is essentially surjective. -/
@[stacks 0G48] #check
  (AlgebraicGeometry.Scheme.DerivedCoh.restrictEssSurj :
    ∀ {X U : Scheme.{u}} (j : U ⟶ X)
      [IsNoetherian X] [IsOpenImmersion j]
      [HasDerivedCategory.{w} (RingedSpace.Coh X.toRingedSpace)]
      [HasDerivedCategory.{w} (RingedSpace.Coh U.toRingedSpace)],
      (functor (ExactFunctor.of
        (AlgebraicGeometry.Scheme.Modules.coherentRestrictFunctor j))).EssSurj)
