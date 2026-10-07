module

public import Mathlib.CategoryTheory.Sites.Coverage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 7.48.2: Let `C` be a site with coverings `Cov(C)`. The topology associated
to `C` is the topology `J` constructed in Lemma 7.48.1, i.e. `Coverage.toGrothendieck`. -/
@[stacks 00ZD] #check @Coverage.toGrothendieck
