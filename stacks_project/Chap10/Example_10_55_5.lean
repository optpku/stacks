/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.Domain
public import ReasLib.RingTheory.Polynomial.Equalizer.Finite
import stacks_project.Chap10.Example_10_55_5.PolynomialEvaluation
import StacksCheckRecall

/-!
# K-groups of the equal-endpoint polynomial ring

@stack 00JG

For a field `k`, the concrete ring is
`Polynomial.equalEndpoint k = {f in k[X] | f(0) = f(1)}`. This file records the two K-group
computations from Example 10.55.5. Generic rank is reused from its ReasLib owner; the former
conductor and clutching calculations are proof infrastructure, not part of the chapter API.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Polynomial.EqualEndpoint.K0

variable (k : Type u) [Field k]

/-- Generic rank is bijective on the finite-module Grothendieck group of the equal-endpoint
polynomial ring. This is the map-level form of `K'_0(R) = Z` in Example 10.55.5. -/
@[stacks 00JG "finite-module generic rank"]
theorem finiteGenericRank_bijective :
    Function.Bijective
      (ModuleCat.K0.Finite.genericRank
        (Polynomial.equalEndpoint k)) := sorry

/-- Example 10.55.5: the finite-module Grothendieck group of the equal-endpoint polynomial ring
is identified with `Z` by generic rank. -/
@[stacks 00JG "finite-module Grothendieck group"]
noncomputable def finiteEquivInt :
    ModuleCat.K0.finite (Polynomial.equalEndpoint k) ≃+ ℤ :=
  AddEquiv.ofBijective
    (ModuleCat.K0.Finite.genericRank (Polynomial.equalEndpoint k))
    (finiteGenericRank_bijective k)

/-- The finite-module equivalence acts by the canonical generic-rank homomorphism. -/
@[simp]
theorem finiteEquivInt_apply
    (x : ModuleCat.K0.finite (Polynomial.equalEndpoint k)) :
    finiteEquivInt k x =
      ModuleCat.K0.Finite.genericRank (Polynomial.equalEndpoint k) x := rfl

/-- Example 10.55.5: the projective Grothendieck group of the equal-endpoint polynomial ring is
`Additive k^x x Z`, with its integer coordinate compatible with the finite-module comparison. -/
@[stacks 00JG "projective Grothendieck group"]
theorem exists_projectiveEquiv :
    ∃ e : ModuleCat.K0.projective (Polynomial.equalEndpoint k) ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        (finiteEquivInt k).toAddMonoidHom.comp
          (ModuleCat.K0.projectiveToFinite (Polynomial.equalEndpoint k)) := sorry

/-- Pointwise form of the compatibility of the integer coordinate with generic rank. -/
theorem exists_projectiveEquiv_snd_apply
    (x : ModuleCat.K0.projective (Polynomial.equalEndpoint k)) :
    ∃ e : ModuleCat.K0.projective (Polynomial.equalEndpoint k) ≃+ Additive kˣ × ℤ,
      (e x).2 = finiteEquivInt k
        (ModuleCat.K0.projectiveToFinite (Polynomial.equalEndpoint k) x) := by
  rcases exists_projectiveEquiv k with ⟨e, he⟩
  exact ⟨e, by simpa using DFunLike.congr_fun he x⟩

end Polynomial.EqualEndpoint.K0


#check @Polynomial.EqualEndpoint.K0.finiteGenericRank_bijective
#check @Polynomial.EqualEndpoint.K0.finiteEquivInt
#check @Polynomial.EqualEndpoint.K0.finiteEquivInt_apply
#check @Polynomial.EqualEndpoint.K0.exists_projectiveEquiv
#check @Polynomial.EqualEndpoint.K0.exists_projectiveEquiv_snd_apply
