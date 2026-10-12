/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.AdjoinRoot

@[expose] public section

/-!
# Local algebra support for Lemma 10.159.1

The reusable local polynomial and monogenic-extension constructions live in
`ReasLib`.  This chapter support file is intentionally a recall block: later
stages should import the shared owners directly rather than depend on a
chapter-local copy of the API.
-/

#check @Polynomial.Local.reduction
#check @Polynomial.Local.exists_monic_lift_of_residueField
#check @AdjoinRoot.Local.quotientEquiv
#check @AdjoinRoot.Local.isLocalRing
#check @AdjoinRoot.Local.mapsMaximalIdeal
#check @AdjoinRoot.Local.residueFieldEquiv
#check @AdjoinRoot.Local.residueFieldEquiv_comp_residueFieldMap
