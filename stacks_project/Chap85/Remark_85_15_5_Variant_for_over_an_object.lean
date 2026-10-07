module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import Mathlib.CategoryTheory.Sites.Over
import StacksCheckRecall

/- Remark 85.15.5 (Variant for over an object) (1): the category SR(C, X) of
semi-representable objects over X is defined by SR(C, X) = SR(C/X). -/
@[stacks 0D89] #check @CategoryTheory.SemiRepresentableFamily.OverFamily

/- Remark 85.15.5 (Variant for over an object) (2): constructions on the site C
apply to the slice site C/X given by J.over X, including component sites of C/K. -/
@[stacks 0D89] #check @CategoryTheory.GrothendieckTopology.over

/- Remark 85.15.5 (Variant for over an object) (3): the iterated slice
(C/X)/(U/X) ≃ C/U identifies summands in the sheaf decomposition
Sh(C/K) = ∏ Sh(C/U_i) for K = {U_i/X}. -/
@[stacks 0D89] #check @CategoryTheory.Over.iteratedSliceEquiv

/- Remark 85.15.5 (Variant for over an object) (4): an arrow f : K ⟶ L in
SR(C, X) induces a morphism of sheaf topoi via overMapPullback on components. -/
@[stacks 0D89] #check @CategoryTheory.GrothendieckTopology.overMapPullback
