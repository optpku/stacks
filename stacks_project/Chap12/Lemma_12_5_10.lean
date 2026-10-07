module

public import ReasLib.CategoryTheory.ShortComplex.Splitting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
variable {S : ShortComplex C}

/- Lemma 12.5.10 (1) [010G]: a chosen section determines its complementary retraction uniquely. -/
@[stacks 010G]
#check @ShortComplex.Splitting.existsUnique_retraction

/- Lemma 12.5.10 (2) [010G]: a chosen retraction determines its complementary section uniquely. -/
#check @ShortComplex.Splitting.existsUnique_section

end
