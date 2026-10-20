module

public import ReasLib.CategoryTheory.Sites.Cohomology.Products
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.12.5

The low-degree product comparison for sheaf cohomology is already owned by
`CategoryTheory.Sheaf.Cohomology.Products`.
-/

open CategoryTheory.Sheaf.Cohomology

@[stacks 060L "degree-zero cohomology of a product"]
#check @productComparison_isIso_zero

@[stacks 060L "degree-one cohomology of a product"]
#check @productComparison_injective_one
