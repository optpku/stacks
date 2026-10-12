/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Henselian.CommonResidueField
import StacksCheckRecall

@[expose] public section

/-!
# Common-residue-field uniqueness for henselian local rings

@stack 08HT

Lemma 10.154.7 is the algebra-equivalence corollary of the reusable
common-residue-field lifting API.  Its canonical owner is
`RingHom.IndEtale.algEquiv_of_commonResidueField`; this chapter file keeps a
tagged recall rather than a second, longer-named wrapper.
-/

/- Lemma 10.154.7 (tag `08HT`): if two henselian local ind-etale
`R`-algebras have residue fields identified with the same field `K`, there is
a unique `R`-algebra equivalence compatible with the maps to `K`. -/
@[stacks 08HT "common residue-field algebra equivalence"]
#check @RingHom.IndEtale.algEquiv_of_commonResidueField
