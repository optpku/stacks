module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering
import StacksCheckRecall

/-!
# Covering morphisms of semi-representable families

The reusable predicates and their forgetful comparison are owned by
`ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering`.
-/

open CategoryTheory

/- Definition 25.3.1 (1): a morphism in `SR(C)` is covering when every component fiber is a
covering family. -/
@[stacks 01G3] #check @SemiRepresentableFamily.covering
#check @SemiRepresentableFamily.mem_covering_iff

/- Definition 25.3.1 (2): a morphism in `SR(C, X)` is covering when its underlying morphism in
`SR(C)` is covering. -/
@[stacks 01G3 "covering morphism of fixed-target semi-representable families"]
#check @SemiRepresentableFamily.OverFamily.covering
#check @SemiRepresentableFamily.OverFamily.mem_covering_iff
