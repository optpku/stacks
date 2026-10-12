/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Topology.Sheaves.Sheaf
import ReasLib.Topology.Sheaf.Space
import StacksCheckRecall

universe u v

open CategoryTheory

variable (X : TopCat.{u})

/- Example 59.11.3: Working this out for the site associated to a topological space,
see Example 59.10.3, gives the usual notion of sheaves. -/
@[stacks 03NN] #check (TopCat.sheaf_eq_siteSheaf X (Type v) : X.Sheaf (Type v) =
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type v))
