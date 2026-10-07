module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.K0
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.120.2 (0FCU)

The reusable comparison between the perfect-derived and finite-projective
Grothendieck groups is owned by
`CategoryTheory.K0Comparison` in ReasLib.

@stack 0FCU
-/

/- Lemma 15.120.2: the Euler-characteristic homomorphism from perfect-derived K₀ to
finite-projective K₀ is an isomorphism. -/
@[stacks 0FCU "Lemma 15.120.2: perfect-derived K₀ comparison"]
#check @CategoryTheory.exists_K0Comparison

#check @CategoryTheory.K0Comparison.bijective
#check @CategoryTheory.K0Comparison.equiv
#check @CategoryTheory.PerfectK0

#print axioms CategoryTheory.exists_K0Comparison
#print axioms CategoryTheory.K0Comparison.equiv

end
