module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Immersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.13.9: for an immersion `i : Z ⟶ X`, the naive cotangent complex of `i`
is isomorphic in `D(𝒪_Z)` to the conormal sheaf of `Z` in `X`, placed in degree zero
and shifted by `1`. -/
@[stacks 0FV2] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.isomorphicConormalShift :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i],
      IsIsomorphic
        (DerivedCategory.Q.obj (AlgebraicGeometry.Scheme.Hom.naiveCotangent i))
        ((shiftFunctor (DerivedCategory Z.Modules) (1 : ℤ)).obj
          ((DerivedCategory.singleFunctor Z.Modules (0 : ℤ)).obj
            (AlgebraicGeometry.Scheme.Hom.conormalSheaf i))))
