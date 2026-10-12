/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
import StacksCheckRecall

/-!
# Stalks of modules on a ringed site

The reusable construction, exactness API, and sheafification comparison are owned by ReasLib at
the arbitrary-site layer.  This file is the source-facing Stacks Project entry.
-/

@[expose] public section

/- Lemma 18.36.3 (1): the stalk functor on sheaves of modules is exact. -/
@[stacks 04EQ "(1)"]
#check (@CategoryTheory.GrothendieckTopology.Point.sheafModuleStalk_exact)

/- Lemma 18.36.3 (2): the stalk functor on presheaves of modules is exact. -/
@[stacks 04EQ "(2)"]
#check (@CategoryTheory.GrothendieckTopology.Point.presheafModuleStalk_exact)

/- Lemma 18.36.3 (3): the canonical comparison from module-presheaf stalks to sheafified
module stalks is invertible. -/
@[stacks 04EQ "(3)"]
#check (@CategoryTheory.GrothendieckTopology.Point.presheafModuleStalkToSheafification_isIso)
