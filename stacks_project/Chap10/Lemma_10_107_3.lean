module

public import ReasLib.RingTheory.Algebra.IsEpi
import StacksCheckRecall

@[expose] public section

/-!
# Base change of algebra epimorphisms

## Canonical recall

Stacks Lemma 10.107.3, tag `04VQ`, is exactly
`Algebra.IsEpi.baseChange`. The reusable statement is owned by ReasLib so
that it is available independently of this chapter-local source entry.

@stack 04VQ
-/

@[stacks 04VQ] #check @Algebra.IsEpi.baseChange
