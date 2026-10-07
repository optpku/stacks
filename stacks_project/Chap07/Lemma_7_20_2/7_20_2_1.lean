module

public import ReasLib.CategoryTheory.Sites.Family.OverlapCofork
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.20.2.1

The fixed-target-family overlap cofork is owned by ReasLib. This source file retains only the
literal presheaf-pullback presentation used by the Chapter 7 argument.
-/

@[expose] public section

/- Lemma 7.20.2 (00XK), overlap presentation: for a fixed-target family `𝒰` with pairwise
pullbacks, the two maps from the coproduct of its pairwise-overlap representables to the coproduct
of its member representables agree after augmentation to the representable presheaf of the fixed
target. Restricting those presheaves along `u` gives the displayed cofork
`∐ u^p h_{V_i ×_V V_j} ⇉ ∐ u^p h_{V_i} ⟶ u^p h_V`. -/
@[stacks 00XK] #check @CategoryTheory.SemiRepresentableFamily.Over.overlapFamily

@[stacks 00XK] #check @CategoryTheory.SemiRepresentableFamily.Over.overlapCofork

@[stacks 00XK] #check @CategoryTheory.SemiRepresentableFamily.Over.whiskerLeftOverlapCofork
