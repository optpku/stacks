module

public import ReasLib.CategoryTheory.Subobject.Quotient
import StacksCheckRecall

@[expose] public section

/- Auxiliary to Definition 12.20.2 (011O): subobject quotient/subquotient infrastructure now
lives in the shared library. -/

@[stacks 011O]
#check @CategoryTheory.subobjectQuotientMap
#check @CategoryTheory.subobjectSubquotient
#check @CategoryTheory.IsSubquotient
#check @CategoryTheory.subobjectSubquotient_isSubquotient_of_le_chain
