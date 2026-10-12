/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import ReasLib.Topology.Sheaf.OpenSubset

/-!
# Ring-sheaf notation on open subspaces

The coefficient-independent restriction API belongs to `ReasLib.Topology.Sheaf.OpenSubset`.
This module supplies the ring-category instances needed by that API and its conventional scoped
notation `𝒪 |_ U`.
-/

@[expose] public section

namespace TopCat

/- Scoped notation for the restriction of a ring sheaf to an open subspace. -/
set_option quotPrecheck false in
scoped notation:80 𝒪:80 " |_ " U:80 =>
  TopCat.Sheaf.OpenSubset.restrict 𝒪 U

end TopCat
