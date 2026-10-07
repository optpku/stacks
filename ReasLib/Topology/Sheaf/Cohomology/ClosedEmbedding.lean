module

public import ReasLib.Topology.Sheaf.ClosedEmbedding
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf cohomology under a closed embedding

The canonical direct-image comparison is invertible in every degree for a closed embedding.
This leaf owns both its objectwise form over an open and its source-facing global specialization.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory.Sheaf.ClosedEmbedding

variable {X Y : TopCat.{u}}

/-- The canonical direct-image cohomology comparison along a closed embedding is an isomorphism
over every open and in every degree. -/
@[stacks 02UV "closed-embedding cohomology comparison"]
theorem comparison_isIso (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    IsIso (CategoryTheory.Sheaf.pushforwardCohomologyMap f F p U) := sorry

/-- The canonical comparison from global cohomology of the direct image to global cohomology on
the source of a closed embedding is an isomorphism in every degree. -/
@[stacks 02UV]
theorem globalComparison_isIso (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (CategoryTheory.Sheaf.pushforwardCohomologyMap f F p (⊤ : Opens Y)) := sorry

end CategoryTheory.Sheaf.ClosedEmbedding
