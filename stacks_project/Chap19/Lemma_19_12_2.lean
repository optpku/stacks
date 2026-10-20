module

public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Grothendieck
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

end CochainComplex
