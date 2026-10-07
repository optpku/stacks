module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Exact
import StacksCheckRecall

/-!
# Exactness of constant abelian sheaves

The reusable exact-functor and short-complex statements are owned by ReasLib.
This file records both the sheaf and underlying-presheaf clauses of the
source lemma.
-/

@[expose] public section

/- Lemma 18.42.1 (093J), sheaf clause: constant abelian sheaves preserve short
exact sequences. -/
@[stacks 093J "(1)"]
#check (@CategoryTheory.ShortComplex.ShortExact.map_constantAbelianSheaf)

/- Lemma 18.42.1 (093J), presheaf clause: the underlying abelian presheaves
remain short exact. -/
@[stacks 093J "(2)"]
#check (@CategoryTheory.ShortComplex.ShortExact.map_constantAbelianPresheaf)

/- The functor-level owner and sectionwise specialization. -/
#check (@CategoryTheory.ConstantSheaf.abelian_exact)
#check (@CategoryTheory.ShortComplex.ShortExact.map_constantAbelianSheaf_app)
