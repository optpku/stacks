/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
# Composition of Bounded-Below Right Derived Functors

The canonical comparison and its injective-acyclicity criterion are owned by the neutral
bounded-below composition API. This chapter file records the textbook entry without rebuilding
injective resolutions or fixing derived-functor parameters through local notation.
-/

open CategoryTheory

/- Lemma 13.22.1 (Stacks 015M): the canonical comparison from the right derived functor of a
bounded-below composite to the composite of right derived functors is an isomorphism exactly when
the first functor sends injective objects to right-acyclic objects for the second functor, assuming
the first two abelian categories have enough injectives and both functors are left exact. -/
@[stacks 015M]
#check @Functor.RightDerived.Composition.BoundedBelow.comparison_isIso_iff

/- The injective-acyclic criterion only needs enough injectives in the source once the three total
right derived functors are already available. -/
#check @Functor.RightDerived.Composition.BoundedBelow.comparison_isIso_iff_injective_rightAcyclic

/- The data-bearing comparison itself is independently reusable. -/
#check @Functor.RightDerived.Composition.BoundedBelow.comparison

/- Its defining factorization through the two derived units is exposed separately. -/
#check @Functor.RightDerived.Composition.BoundedBelow.comparison_fac

/- The componentwise factorization removes repeated `NatTrans.congr_app` glue in applications. -/
#check @Functor.RightDerived.Composition.BoundedBelow.comparison_fac_app

/- Invertibility of a comparison component is invariant under a bounded-below quasi-isomorphism. -/
#check @Functor.RightDerived.Composition.BoundedBelow.comparison_app_isIso_iff_of_quasiIso
