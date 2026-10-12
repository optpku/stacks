/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.DeltaFunctor
import StacksCheckRecall

@[expose] public section

/- Lemma 20.10.2 (Tag 01EK): the cohomological Cech delta-functor owner is the generic exact
cochain-complex construction specialized to ringed-site presheaf modules. -/

open CategoryTheory
open SheafOfModules.RingedSite.Cech

@[stacks 01EK] #check @degree
@[stacks 01EK] #check @map_shortExact
@[stacks 01EK] #check @connecting
@[stacks 01EK] #check @deltaFunctor
@[stacks 01EK] #check @deltaFunctor_obj
@[stacks 01EK] #check @deltaFunctor_obj_obj
@[stacks 01EK] #check @deltaFunctor_δ
