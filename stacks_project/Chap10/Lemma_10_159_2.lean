/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.IndEtaleExtension
import StacksCheckRecall

/-!
# Filtered étale residue-field extensions

@stack 09E0

The source's filtered system is represented at the library boundary by the
canonical `RingHom.IndEtale` predicate.  The local map and residue-field
equivalence remain explicit in the ReasLib producer.
-/

@[expose] public section

@[stacks 09E0 "ind-etale owner"]
#check @RingHom.IndEtale
@[stacks 09E0 "etale bridge"]
#check @RingHom.IndEtale.ofEtale
@[stacks 09E0 "source bridge"]
#check @IsLocalRing.ResidueField.exists_indEtale_localExtension
