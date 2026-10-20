module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Polynomial
import StacksCheckRecall

/-!
# Lemma 15.82.1 (065F)

@stack 065F
-/

@[expose] public section

/- Lemma 15.82.1: after viewing a derived `R`-complex over `R[X]` through evaluation at zero,
derived extension back to `R` is isomorphic to the complex together with its shift. -/
@[stacks 065F "derived self-intersection of polynomial evaluation at zero"]
#check @CategoryTheory.ModuleCat.DerivedExtension.Polynomial.evalZero_selfIntersection
