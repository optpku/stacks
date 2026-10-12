/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.Domain
public import ReasLib.RingTheory.Polynomial.Equalizer.Finite
import StacksCheckRecall

/-!
# Generic rank over the equal-endpoint algebra

@stack 00JG
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

section

variable (k : Type u) [Field k]

/-- The ordinary finite rank of a projective module over the equal-endpoint algebra, viewed in
`ℤ` for compatibility with Grothendieck groups. -/
@[stacks 00JG "rank of an equal-endpoint projective module"]
noncomputable abbrev equalEndpointProjectiveRank
    (M : ModuleCat.FiniteProjective (Polynomial.equalEndpoint k)) : ℤ :=
  (Module.finrank (Polynomial.equalEndpoint k) M.obj : ℤ)

/-- The generic-rank homomorphism on projective K0 of the equal-endpoint ring. -/
@[stacks 00JG "generic rank on the equal-endpoint projective K0"]
noncomputable abbrev equalEndpointProjectiveRankMap :
    ModuleCat.K0.projective (Polynomial.equalEndpoint k) →+ ℤ :=
  ModuleCat.K0.Projective.genericRank (Polynomial.equalEndpoint k)

/-- Projective generic rank evaluates on a generator by its ordinary finite rank. -/
@[stacks 00JG "generic rank on equal-endpoint projective generators"]
theorem equalEndpointProjectiveRankMap_apply_of
    (M : ModuleCat.FiniteProjective (Polynomial.equalEndpoint k)) :
    equalEndpointProjectiveRankMap k
        (ModuleCat.K0.projectiveOf (Polynomial.equalEndpoint k) M) =
    equalEndpointProjectiveRank k M :=
  ModuleCat.K0.Projective.genericRank_of (Polynomial.equalEndpoint k) M

end

#check @equalEndpointProjectiveRank
#check @equalEndpointProjectiveRankMap
#check @equalEndpointProjectiveRankMap_apply_of
