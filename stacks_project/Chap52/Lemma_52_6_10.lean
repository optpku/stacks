module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.FunctorialCech
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 52.6.10: existence of a functorial augmented Čech complex for finitely generated ideals. -/
@[stacks 099D] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.existsFunctorialCechComplex :
    Nonempty (CategoryTheory.DerivedCategory.LocalCohomology.FunctorialCechComplex.{u}))
