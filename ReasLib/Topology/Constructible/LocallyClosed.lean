/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible

/-!
# Constructibility of Locally Closed Sets

This leaf contains the compactness and retrocompact-complement criterion for a
locally closed subset of a prespectral quasi-separated space.
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace Topology

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
variable {T : Set X}

/-- A compact locally closed subset with retrocompact complement is
constructible in a prespectral quasi-separated space. -/
theorem IsLocallyClosed.isConstructible_of_isCompact_of_retrocompact_compl
    (hT_loc : IsLocallyClosed T) (hT_compact : IsCompact T) (hTc_retro : IsRetrocompact Tᶜ) :
    IsConstructible T := sorry

end Topology
