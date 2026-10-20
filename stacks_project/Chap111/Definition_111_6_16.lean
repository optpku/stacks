/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Artinian
public import ReasLib.Topology.Noetherian.Chains
import StacksCheckRecall

@[expose] public section

/- Companion: the canonical Noetherian-space predicate is
`TopologicalSpace.NoetherianSpace`, equivalently `WellFoundedLT (TopologicalSpace.Closeds X)`
by `TopologicalSpace.noetherianSpace_TFAE`. -/
#check (TopologicalSpace.NoetherianSpace : (X : Type _) → [TopologicalSpace X] → Prop)

namespace TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/- Definition 111.6.16: a topological space `X` is Noetherian when every decreasing
sequence of closed subsets of `X` stabilizes. -/
@[stacks 027F] #check (TopologicalSpace.noetherianSpace_iff_antitone_closeds :
  NoetherianSpace X ↔ ∀ Z : ℕ → Closeds X, Antitone Z → ∃ n, ∀ m, n ≤ m → Z n = Z m)

/- Companion: a topological space `X` is Artinian when every increasing
sequence of closed subsets of `X` stabilizes. -/
#check (TopologicalSpace.ArtinianSpace : (X : Type u) → [TopologicalSpace X] → Prop)

/- Companion: increasing closed chains stabilize in an Artinian space. -/
#check (artinianSpace_iff :
  ArtinianSpace X ↔ ∀ Z : ℕ →o Closeds X, ∃ n, ∀ m, n ≤ m → Z n = Z m)

/- Companion: Artinianity is the descending chain condition on open subsets. -/
#check (artinianSpace_iff_wellFoundedLT_opens : ArtinianSpace X ↔ WellFoundedLT (Opens X))

/- Companion: finite topological spaces are Artinian. -/
#check (Finite.to_artinianSpace : [Finite X] → ArtinianSpace X)

end TopologicalSpace
