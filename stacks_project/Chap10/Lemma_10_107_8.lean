module

public import ReasLib.RingTheory.Algebra.IsEpi
import StacksCheckRecall

@[expose] public section

/-!
# Epimorphisms out of fields

## Canonical recall

Stacks Lemma 10.107.8, tag `04VV`, is exactly
`Algebra.IsEpi.subsingleton_or_nonempty_algEquiv`. The reusable statement is
owned by ReasLib rather than duplicated as a chapter-local alias.

@stack 04VV
-/

@[stacks 04VV] #check @Algebra.IsEpi.subsingleton_or_nonempty_algEquiv
