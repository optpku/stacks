/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.36.1 (1): below the top fiber degree, proper pushforward of
`c₁(𝒪_P(1))^s ∩ π^* α` vanishes. -/
@[stacks 02TW] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.pushforwardC1PowerCap_eq_zero_of_lt :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
      (k : ℤ) (s : ℕ) (_ : s < q)
      (α : @AlgebraicGeometry.ChowGroup X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k),
      AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.pushforwardC1PowerCap
        δ p E q π hπ k s α = 0)

/- Lemma 42.36.1 (2): in the top fiber degree, proper pushforward of
`c₁(𝒪_P(1))^q ∩ π^* α` is `α`. -/
@[stacks 02TW] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.pushforwardTopC1PowerCap_eq_self :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
      (k : ℤ)
      (α : @AlgebraicGeometry.ChowGroup X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k),
      AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.pushforwardTopC1PowerCap
        δ p E q π hπ k α = α)
