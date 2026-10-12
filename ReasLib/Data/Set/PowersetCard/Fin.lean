/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Hom.PowersetCard

/-!
# Initial subsets of `Fin`

This leaf packages the initial segment of a finite ordinal as a fixed-cardinality
subset. It is independent of the matrix and presentation applications.
-/

@[expose] public section

namespace Set.powersetCard

variable {c n : ℕ}

/-- The first `c` elements of `Fin n`, as a `c`-element subset. -/
def initial (hc : c ≤ n) : Set.powersetCard (Fin n) c :=
  ofFinEmbEquiv (Fin.castLEOrderEmb hc)

end Set.powersetCard
