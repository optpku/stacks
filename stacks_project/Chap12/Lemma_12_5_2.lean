module

public import ReasLib.CategoryTheory.Abelian.Opposite
import StacksCheckRecall

@[expose] public section

/- Lemma 12.5.2 (1) [010A]: preadditive structure passes canonically to the opposite category and
can be recovered explicitly in the reverse direction. -/
@[stacks 010A]
#check @CategoryTheory.instPreadditiveOpposite

#check @CategoryTheory.Preadditive.ofOpposite

/- For the Stacks notion of an additive category, finite products pass to the opposite through
the canonical finite-biproduct structure; the reverse construction remains explicit. -/
#check @CategoryTheory.Preadditive.hasFiniteProducts_opposite

#check @CategoryTheory.Preadditive.hasFiniteProductsOfOpposite

/- Lemma 12.5.2 (2) [010A]: abelian structure has the same canonical forward instance and an
explicit reverse construction without an instance loop. -/
#check @CategoryTheory.instAbelianOpposite

#check @CategoryTheory.Abelian.ofOpposite

end
