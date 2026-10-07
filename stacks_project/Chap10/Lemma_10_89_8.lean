module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.89.8

@stack 0EGI
-/

/- Chap10 Lemma 10 89 8: the quotient in an exact, right-surjective short complex is
Mittag-Leffler when the kernel term is finite and the middle term is Mittag-Leffler. -/
@[stacks 0EGI]
#check @CategoryTheory.ShortComplex.mittagLeffler_X₃_of_exact_of_finite_of_mittagLeffler
