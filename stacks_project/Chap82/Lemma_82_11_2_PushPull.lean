/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap67.Lemma_67_45_9
public import stacks_project.Chap67.Lemma_67_46_6
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle
public import stacks_project.Chap82.Lemma_82_8_2_Pushforward
public import stacks_project.Chap82.Lemma_82_10_5_Pullback
public import stacks_project.Chap82.Lemma_82_11_2_RelativeDimension

/-!
# Push-pull of cycles along finite locally free morphisms

For a finite locally free morphism of rank `d` of good algebraic spaces, the
composite of flat pullback of relative dimension `0` with proper pushforward
acts on `k`-cycles by multiplication by `d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- For a finite locally free morphism of rank `d`, the composite of flat
pullback of relative dimension `0` with proper pushforward multiplies every
`k`-cycle by `d`. -/
theorem properPushforward_flatPullback_nsmul {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (d : ℕ) [FiniteLocallyFreeOfRank f d]
    (hf : f ≫ pY = pX) (k : ℤ) {α : Function.locallyFinsupp (Points Y) ℤ}
    (hα : α ∈ cycleGroup pY δ k) :
    properPushforwardCycle pX pY δ f hf
        (flatPullbackCycle pY pX δ f 0 hf k α) =
      d • α :=
  sorry

/-- The push-pull formula on the associated cycle of an integral closed
subspace of `δ`-dimension `k`. -/
theorem properPushforward_flatPullback_integral {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (d : ℕ) [FiniteLocallyFreeOfRank f d]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y) [IsIntegral Z.X]
    (hZ : closedSubspaceDeltaDimension pY δ Z = (k : EInt)) :
    properPushforwardCycle pX pY δ f hf
        (flatPullbackCycle pY pX δ f 0 hf k
          (@ClosedSubspace.cycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY)
            Z (relativeDimensionFunction pY δ) k)) =
      d • @ClosedSubspace.cycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY) Z
          (relativeDimensionFunction pY δ) k :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
