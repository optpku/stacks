module

import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Exercise 111.30.9

The source-facing existence of a degree-zero filtered-injective replacement of an object of
`Filᶠ(C)` is owned by `CochainComplex.FilteredInjectivePlus.exists_quasiIso_single` in ReasLib.
-/

namespace CochainComplex.FilteredInjectivePlus

/- Exercise 111.30.9

In an abelian category with enough injectives, every object of `Filᶠ(C)` admits a morphism
`A[0] ⟶ I^•` to a complex of finite filtered-injective objects that vanishes in negative degrees
and is a filtered quasi-isomorphism. -/
@[stacks 028G] #check
  (CochainComplex.FilteredInjectivePlus.exists_quasiIso_single :
    ∀ {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
      [CategoryTheory.EnoughInjectives C],
      (A : CategoryTheory.FilteredObject.Finite.category C) →
        ∃ (I : CochainComplex.FilteredInjectivePlus C)
          (f : (CochainComplex.singleFunctor (CategoryTheory.FilteredObject.Finite.category C)
              (0 : ℤ)).obj A ⟶
            (CochainComplex.FilteredInjectivePlus.ι C).obj I),
          ((CochainComplex.FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0 ∧
            CategoryTheory.FilteredObject.Finite.CochainComplex.quasiIso C f)

end CochainComplex.FilteredInjectivePlus
