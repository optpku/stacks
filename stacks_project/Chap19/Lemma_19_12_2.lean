/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Grothendieck
public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.SubcomplexSupply
import StacksCheckRecall

@[expose] public section

/-!
# Small Acyclic Subcomplexes

The reusable predicates, the termwise subcomplex constructor, and the Grothendieck-category
existence theorem are owned by ReasLib. This file records the source statement as a typed check.
-/

open CategoryTheory

universe w v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/- Lemma 19.12.2: one cardinal controls both the nonzero bounded-above acyclic subcomplexes and
the coproduct presentations of all acyclic cochain complexes. -/
@[stacks 079K] #check
  (SmallAcyclic.exists_bound C :
    ∃ kappa : Cardinal.{max u v + 1},
      SmallAcyclic.IsUniformBound C kappa)

#check @HomologicalComplex.TermwiseSubcomplex
#check @HomologicalComplex.SubobjectCardinal.BoundedBy
#check @SmallAcyclic.BoundedBy
#check @SmallAcyclic.BoundedBy.ofTermwise
#check @SmallAcyclic.IsUniformBound
#check @SmallAcyclic.isUniformBound_iff

/- Lemma 19.12.2 (1), proof: the specified supply is constructed termwise from the native
separator, with the source cardinal and descending kernel-preimage recursion. -/
#check
  (SmallAcyclic.Grothendieck.subcomplexSupply C :
    SmallAcyclic.SubcomplexSupply C (SmallAcyclic.Grothendieck.bound C))
#check @SmallAcyclic.Grothendieck.growth
#check @SmallAcyclic.Grothendieck.exists_nonzero_generator_map
#check @SmallAcyclic.Grothendieck.refinement
#check @SmallAcyclic.Grothendieck.lower
#check @SmallAcyclic.Grothendieck.descend
#check @SmallAcyclic.Grothendieck.termwise

end CochainComplex
