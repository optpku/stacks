/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.RationalEquivalence

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- Lemma 42.38.3: Intersection with the `j`th Chern class of a finite locally free
module sends rationally equivalent degree-`k` cycles to the same class in
`CH_(k-j)(X)`. -/
@[stacks 02U7]
#check
  (AlgebraicGeometry.ChowGroup.chernClassCap_eq_of_rationallyEquivalent :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
      (c : (j : Fin (r + 1)) →
        CycleGroup X (p.relativeDimensionFunction δ) k →+
          @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)))
      (hc : ProjectiveBundle.IsChernClassCap δ p E r π hπ k c)
      (α β : CycleGroup X (p.relativeDimensionFunction δ) k)
      (h_rational : @RationalEquivalence.RationallyEquivalent X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k α β)
      (j : Fin (r + 1)),
      c j α = c j β)

end AlgebraicGeometry.ChowGroup
