/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.3.3

Pullback of descent data is already objectwise and functorially available in mathlib's canonical
`Pseudofunctor.DescentData` presentation.  The bundled family-morphism form and its same-base
comparison remain ergonomic ReasLib bridges.
-/

namespace CategoryTheory

/- Lemma 8.3.3 (1): pull a descent datum back along a morphism of covering families. -/
@[stacks 02ZD "(1) pullback descent datum"]
#check @DescentDatum.Pullback.functorOfHom_obj_obj

/- Lemma 8.3.3 (2): pullback is functorial on descent data. -/
@[stacks 02ZD "(2) pullback functor on descent data"]
#check @DescentDatum.Pullback.functorOfHom

/- Lemma 8.3.3 (3): two pullback functors with the same base map are canonically naturally
isomorphic. -/
@[stacks 02ZD "(3) canonical pullback-functor comparison"]
#check @DescentDatum.Pullback.isoOfHom

/- Generic Mathlib owners and further bundled computations. -/
#check @Pseudofunctor.DescentData.pullFunctorObj
#check @Pseudofunctor.DescentData.pullFunctor
#check @Pseudofunctor.DescentData.pullFunctorIso
#check @DescentDatum.Pullback.functorOfHom_map_hom
#check @DescentDatum.Pullback.functorOfHom_obj_hom
#check @DescentDatum.Pullback.functorOfRefinement
#check @DescentDatum.Pullback.isoOfHom_hom_app_hom

end CategoryTheory
