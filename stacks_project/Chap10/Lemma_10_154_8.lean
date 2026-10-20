module

public import ReasLib.RingTheory.Henselian.DirectLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.154.8

@stack 04GI

The source statement is a direct-limit closure result for local commutative
rings.  Its reusable owners are the two neutral instances
`Ring.DirectLimit.colimitHenselianLocalRing` and
`Ring.DirectLimit.colimitStrictHenselianLocalRing`; the direct-limit carrier,
directed-system assumptions, and local transition maps are inherited without
repackaging them in a chapter-specific structure.
-/

/- Lemma 10.154.8 (1), Stacks tag `04GI`: a directed colimit of henselian
local rings along local homomorphisms is henselian. -/
@[stacks 04GI "henselian local rings"]
#check @Ring.DirectLimit.colimitHenselianLocalRing

/- Lemma 10.154.8 (2), Stacks tag `04GI`: a directed colimit of strictly
henselian local rings along local homomorphisms is strictly henselian. -/
@[stacks 04GI "strictly henselian local rings"]
#check @Ring.DirectLimit.colimitStrictHenselianLocalRing

#print axioms Ring.DirectLimit.colimitHenselianLocalRing
#print axioms Ring.DirectLimit.colimitStrictHenselianLocalRing
