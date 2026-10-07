module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.70.6 (0DW2)

@stack 0DW2
-/

/- Lemma 15.70.6, Stacks `0DW2`: over a Noetherian ring, a bounded-below complex with finite
cohomology has finite injective dimension exactly when sufficiently high extensions from all
ideal quotients above a fixed ideal in the Jacobson radical vanish. -/
@[stacks 0DW2 "Lemma 15.70.6, ideal-quotient criterion for finite injective dimension"]
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension.iff_eventually_idealQuotient_ext
