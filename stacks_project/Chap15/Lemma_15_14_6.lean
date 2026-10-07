module

import StacksCheckRecall
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.FreeExtension

@[expose] public section

/- Lemma 15.14.6, tag `0DCR`: for every commutative ring `A` there is an
injective `A`-algebra `B` which is free over `A`, is a filtered colimit of
finite-free `A`-algebras, and is absolutely integrally closed.  The
root-adjoining stages are implementation detail of the shared owner. -/
/-!
@stack 0DCR
-/

@[stacks 0DCR "Lemma 15.14.6"]
#check @IsAbsolutelyIntegrallyClosed.exists_freeExtension

#check @RingHom.FiniteFree
#check @RingHom.finiteFree_algebraMap
#check @RingHom.IndFiniteFree
#check @RingHom.IndFiniteFree.Raw
#check @RingHom.IndFiniteFree.ofRaw
#check @RingHom.IndFiniteFree.ofFiniteFree
