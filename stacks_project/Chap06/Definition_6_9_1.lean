/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import StacksCheckRecall

@[expose] public section

/- The equalizer-products predicate exactly packages the source diagram for every indexed open
cover, while the comparison theorem identifies it with mathlib's site-theoretic sheaf predicate.
Keeping both as direct recalls avoids a duplicate local predicate and makes either formulation
available to downstream items. -/

/- Definition 6.9.1: for a `C`-valued presheaf on a topological space `X`, the Stacks equalizer
diagram condition for every open covering is the canonical mathlib predicate
`TopCat.Presheaf.IsSheafEqualizerProducts`. -/
@[stacks 0072 "equalizer-products sheaf condition"]
recall TopCat.Presheaf.IsSheafEqualizerProducts

/- This source-facing equalizer-products sheaf condition is equivalent to the canonical sheaf
predicate `TopCat.Presheaf.IsSheaf`. -/
@[stacks 0072 "comparison with the canonical sheaf predicate"]
recall TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
