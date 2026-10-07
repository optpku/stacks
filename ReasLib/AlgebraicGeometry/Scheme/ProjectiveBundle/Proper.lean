module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic

/-!
# Properness of projective bundles

This file records properness of a represented projective bundle associated to a positive-rank
finite locally free module.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.Representation

/-- A represented projective bundle of a rank-`q + 1` finite locally free module is proper
over its base. -/
theorem isProperOfFiniteLocallyFree {X P : Scheme.{u}} {E : X.Modules} {π : P ⟶ X}
    (hπ : ProjectiveBundle.Representation π E) (q : ℕ)
    [Modules.IsFiniteLocallyFreeOfRank (q + 1) E] : IsProper π := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
