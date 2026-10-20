module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.SerreFunctor
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 57.4.1: for a proper Gorenstein scheme over a field, tensoring perfect derived modules
with the proper dualizing complex is a Serre functor. -/
@[stacks 0FY8] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.tensorFunctor_isSerre :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsProper X.hom]
      [AlgebraicGeometry.Scheme.Gorenstein X.left],
      CategoryTheory.Functor.IsSerreWith
        (AlgebraicGeometry.Scheme.ModuleDerived.Perfect.linearFor X.hom)
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.tensorFunctor X))
