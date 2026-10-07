module

public import ReasLib.CategoryTheory.Sites.Cech.Universal
public import ReasLib.CategoryTheory.Sites.Cech.Derived
import StacksCheckRecall

@[expose] public section

/- Lemma 21.9.6 (Tag 03AU): fixed-target Cech cohomology is a universal delta functor and is
computed by the right derived functor of degree-zero Cech cohomology. -/

@[stacks 03AU "universality of the fixed-target Cech delta functor"]
#check @CategoryTheory.Cech.FixedTarget.deltaFunctor_isUniversal

@[stacks 03AU "fixed-target Cech cohomology as a right derived functor"]
#check @CategoryTheory.Cech.FixedTarget.cohomologyFunctor_isIsomorphic_rightDerived

@[stacks 03AU "fixed-target Cech complex comparison with an injective resolution"]
#check @CategoryTheory.Cech.FixedTarget.complex_quasiIso_to_cohomologyZero
