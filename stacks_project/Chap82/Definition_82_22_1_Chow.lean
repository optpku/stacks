module

public import stacks_project.Chap82.Definition_82_15_1_Chow
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward

/-!
# Chow-level pushforward along closed subspace immersions

The weight-1 closed-immersion pushforward of cycles induces a homomorphism of
Chow groups by preserving rational equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- Closed-immersion pushforward sends rationally trivial cycles to rationally
trivial cycles. -/
theorem closedImmersionPushforward_mem_boundaries (W : ClosedSubspace X) (k : ℤ)
    [QuasiSeparated (W.ι ≫ f)] [LocallyOfFiniteType (W.ι ≫ f)] :
    RationalEquivalence.boundaries (W.ι ≫ f) δ k ≤
      (RationalEquivalence.boundaries f δ k).comap
        (closedImmersionPushforward f δ W k) :=
  sorry

/-- Pushforward of degree-`k` Chow classes along the closed immersion of a
closed subspace. -/
noncomputable def chowPushforward (W : ClosedSubspace X) (k : ℤ)
    [QuasiSeparated (W.ι ≫ f)] [LocallyOfFiniteType (W.ι ≫ f)] :
    Hom.chowGroup (W.ι ≫ f) δ k →+ Hom.chowGroup f δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries (W.ι ≫ f) δ k)
    (RationalEquivalence.boundaries f δ k)
    (closedImmersionPushforward f δ W k)
    (closedImmersionPushforward_mem_boundaries f δ W k)

/-- Chow-class pushforward is induced by cycle pushforward on representatives. -/
theorem chowPushforward_chowMk (W : ClosedSubspace X) (k : ℤ)
    [QuasiSeparated (W.ι ≫ f)] [LocallyOfFiniteType (W.ι ≫ f)]
    (α : Hom.cycleGroup (W.ι ≫ f) δ k) :
    chowPushforward f δ W k (Hom.chowMk (W.ι ≫ f) δ k α) =
      Hom.chowMk f δ k (closedImmersionPushforward f δ W k α) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
