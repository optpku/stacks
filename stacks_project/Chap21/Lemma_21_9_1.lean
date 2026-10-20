module

public import ReasLib.CategoryTheory.Sites.Cech.DeltaFunctor
import StacksCheckRecall

@[expose] public section

/- Lemma 21.9.1 (Tag 03AQ): for a fixed-target family whose iterated fibre products exist,
the associated additive-presheaf Cech cochain functor is exact. -/

@[stacks 03AQ "fixed-target Cech cochain functor"]
#check @CategoryTheory.Cech.FixedTarget.cochainFunctor

@[stacks 03AQ "exact fixed-target Cech cochain functor"]
#check @CategoryTheory.Cech.FixedTarget.cochainFunctor_exact
