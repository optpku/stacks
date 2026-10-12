/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Colimit

/-!
# Lemma 15.59.8

@stack 06Y3

The reusable ModuleCat bridge is `CochainComplex.isKFlat_colimit_of_isFiltered`; its categorical
core is `CochainComplex.IsKFlat.colimit_of_isFiltered`.  Taking the indexing category to be `ℕ`
recovers the sequential-system clause.
-/

@[expose] public section

/- Lemma 15.59.8 (06Y3): filtered colimits, including sequential colimits, preserve K-flatness. -/
@[stacks 06Y3 "filtered colimits of K-flat complexes are K-flat"]
#check @CochainComplex.isKFlat_colimit_of_isFiltered

#check @CochainComplex.IsKFlat.colimit_of_isFiltered
