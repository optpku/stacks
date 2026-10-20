module

public import ReasLib.CategoryTheory.Sites.Point.Skyscraper.Exact
import StacksCheckRecall

@[expose] public section

/- Lemma 18.37.1 (1): direct image from abelian groups to skyscraper sheaves is exact. -/
@[stacks 05V7 "(1)"]
#check @CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctor_exact

/- Lemma 18.37.1 (2): the fiber--skyscraper counit is functorially split epic, equivalently
giving the source decomposition `p⁻¹(p_* A) ≅ A ⊞ I(A)`. -/
@[stacks 05V7 "(2)"]
#check @CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_counit_isSplitEpi
