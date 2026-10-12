/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.CohomologicalDescent
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.TopCat

/-!
# Cohomological descent for open hypercoverings

An open hypercovering supplies a simplicial family of opens, hence a canonical augmented
simplicial topological space.  All degreewise pullback, page-one, descent, and convergence
interfaces are inherited from the category-level `SimplicialObject.Augmented` owner.  The source
remark points forward to the cohomological-descent theorem; it does not provide an existence
construction, so this leaf is a source-facing recall rather than an unconditional existence API.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace SSet.OpenHypercovering

variable {X : TopCat.{max u v}} (H : OpenHypercovering.{max u v, v} X)

/-- Remark 25.11.2 (Tag 02N9): the open-hypercovering spectral-sequence assertion is the
cohomological-descent interface for the associated augmented simplicial space.  Its existence is
left to the later descent theorem; downstream code should use the canonical predicate and its
`of_total` constructor after supplying the relevant comparison data. -/
@[stacks 02N9 "open-hypercover descent spectral-sequence interface"]
abbrev simplicialSpace.descentPredicate (ℱ : X.Sheaf AddCommGrpCat.{max u v}) :
    (CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v} 1 → Prop) :=
  (SSet.OpenFamily.simplicialSpace.augmented H.family).IsDescentSpectralSequence ℱ

end SSet.OpenHypercovering

namespace SSet.OpenHypercovering.ulift

variable {X : Type u} [TopologicalSpace X]
variable (H : OpenHypercovering.{u, v} X)

/-- The cohomological-descent predicate after the canonical universe lift of the base space. -/
@[stacks 02N9 "cohomological descent interface after universe lift"]
abbrev descentPredicate
  (ℱ : (TopCat.of (ULift.{v} X)).Sheaf AddCommGrpCat.{max u v}) :
    CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v} 1 → Prop :=
  (SSet.OpenFamily.simplicialSpace.augmented
    (X := TopCat.of (ULift.{v} X)) H.ulift.family).IsDescentSpectralSequence ℱ

end SSet.OpenHypercovering.ulift
