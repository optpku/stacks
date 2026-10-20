module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.PID
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.55.3

@stack 0FJ8

Over a principal ideal domain, generic rank gives the canonical identifications of both the
finite-module and finite-projective Grothendieck groups with `ℤ`.  The comparison map is recorded
directly in those coordinates.
-/

/- Example 10.55.3: generic rank identifies `K'_0(R)` with `ℤ` for a principal ideal domain. -/
@[stacks 0FJ8 "finite-module Grothendieck group"]
#check @CategoryTheory.ModuleCat.K0.Finite.genericRankEquiv

/- Example 10.55.3: ordinary rank identifies `K₀(R)` with `ℤ` for a principal ideal domain. -/
@[stacks 0FJ8 "finite-projective Grothendieck group"]
#check @CategoryTheory.ModuleCat.K0.Projective.genericRankEquiv

/- The projective-to-finite comparison acts as the identity in the two generic-rank
coordinates. -/
@[stacks 0FJ8 "projective-to-finite comparison"]
#check @CategoryTheory.ModuleCat.K0.genericRankEquiv_projectiveToFinite_apply

/- Equivalently, the comparison map is obtained by passing through the two explicit
generic-rank equivalences. -/
@[stacks 0FJ8 "projective-to-finite comparison formula"]
#check @CategoryTheory.ModuleCat.K0.projectiveToFinite_eq_viaGenericRank
