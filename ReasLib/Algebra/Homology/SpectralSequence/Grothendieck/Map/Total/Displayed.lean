/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total

/-!
# Canonical displayed owner for Grothendieck total realizations

The Grothendieck total category is definitionally the total category of
`displayedCategory`.  This compatibility leaf intentionally adds no second category or identity
equivalence: clients should import the neutral `DisplayedCategory.Total` API directly.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence

/- The old displayed presentation is now a canonical recall of the generic total owner. -/

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence
