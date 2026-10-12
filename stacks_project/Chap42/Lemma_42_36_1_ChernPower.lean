/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.Representation

/-- Composing a represented rank-`q + 1` projective bundle with a locally finite type
morphism is locally of finite type. -/
theorem locallyOfFiniteTypeComp
    {S X P : Scheme.{u}} {E : X.Modules} {π : P ⟶ X}
    (hπ : ProjectiveBundle.Representation π E) (q : ℕ) (p : X ⟶ S)
    [Modules.IsFiniteLocallyFreeOfRank (q + 1) E] [LocallyOfFiniteType p] :
    LocallyOfFiniteType (π ≫ p) :=
  AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.locallyOfFiniteTypeComp
    hπ p (q + 1)

end AlgebraicGeometry.Scheme.ProjectiveBundle.Representation

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

export Formula (pullbackThenC1PowerCap pullbackThenC1PowerCap_apply)

/- The compatibility surface exposes the canonical pullback-and-Chern-power map under the
historical projective-bundle namespace. -/
#check
  (pullbackThenC1PowerCap :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
      (k : ℤ) (s : ℕ),
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k →+
        Formula.totalSpaceChowGroup δ p E (q + 1) π hπ
          (k + (q : ℤ) - (s : ℤ)))

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
