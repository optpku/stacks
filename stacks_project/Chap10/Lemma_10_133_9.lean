module

public import ReasLib.Algebra.Module.PrincipalParts.Diagonal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.9

@stack 0H90

Lemma 10.133.9 (Tag 0H90): the order-`k` principal-parts module is the
quotient of `S ⊗[R] M` by the `(k + 1)`st power of the diagonal ideal.  The
tensor action and quotient presentation are owned by `PrincipalParts.Diagonal`,
which reuses the scoped right-factor tensor-module construction rather than
rebuilding a chapter-local action.
-/

@[stacks 0H90 "diagonal-ideal presentation of principal parts"]
#check @PrincipalParts.Diagonal.powerSubmodule

#check @PrincipalParts.Diagonal.relation
#check @PrincipalParts.Diagonal.quotient
#check @PrincipalParts.Diagonal.toQuotient
#check @PrincipalParts.Diagonal.fromQuotient
#check @PrincipalParts.Diagonal.equiv
#check @PrincipalParts.Diagonal.equiv.apply_universalDifferential
