module

public import stacks_project.Chap82.Lemma_82_10_5_Pullback
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Definition_82_6_1_AssociatedCycle
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Flat pullback of associated cycles

In Situation 82.2.1, for good `X`, `Y / B` and a flat morphism `f : X ⟶ Y` of
relative dimension `r`, inverse images of closed subspaces and pullbacks of
coherent modules increase `δ`-dimension by at most `r`, and their associated
cycles are compatible with flat pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.10.5 (1): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. If `Z ⊂ Y` is a
closed subspace with `dim_δ(Z) ≤ k`, then `dim_δ(f⁻¹(Z)) ≤ k + r`. -/
@[stacks 0EPB]
theorem closedSubspaceDeltaDimension_inverseImage_le {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y)
    (hZ : closedSubspaceDeltaDimension pY δ Z ≤ (k : EInt)) :
    closedSubspaceDeltaDimension pX δ (Z.inverseImage f) ≤
      (k + (r : ℤ) : EInt) :=
  sorry

/-- Lemma 82.10.5 (2): In Situation 82.2.1, under the hypotheses of (1),
`[f⁻¹(Z)]_{k+r} = f^*[Z]_k` in `Z_{k+r}(X)`. -/
@[stacks 0EPB]
theorem flatPullback_closedSubspaceCycle {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y)
    (hZ : closedSubspaceDeltaDimension pY δ Z ≤ (k : EInt)) :
    @ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian pX)
        (Z.inverseImage f) (relativeDimensionFunction pX δ) (k + (r : ℤ)) =
      flatPullbackCycle pY pX δ f r hf k
        (@ClosedSubspace.cycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY) Z
          (relativeDimensionFunction pY δ) k) :=
  sorry

/-- Lemma 82.10.5 (3): In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a flat morphism of relative dimension `r`. If `F` is a coherent
`𝒪_Y`-module with `dim_δ(Supp(F)) ≤ k`, then `dim_δ(Supp(f^* F)) ≤ k + r`. -/
@[stacks 0EPB]
theorem moduleSupportDeltaDimension_pullback_le {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (F : Y.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pY δ F ≤ (k : EInt)) :
    @moduleSupportDeltaDimension S B X _ _ pX _ _ δ _
        ((Modules.pullback f).obj F)
        (@Modules.instIsCoherent_pullback S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (LocallyOfFiniteType.isLocallyNoetherian pY) f F _) ≤
      (k + (r : ℤ) : EInt) :=
  sorry

/-- Lemma 82.10.5 (4): In Situation 82.2.1, under the hypotheses of (3),
`f^*[F]_k = [f^* F]_{k+r}` in `Z_{k+r}(X)`. -/
@[stacks 0EPB]
theorem flatPullback_moduleCycle {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) (F : Y.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pY δ F ≤ (k : EInt)) :
    flatPullbackCycle pY pX δ f r hf k (moduleCycle pY δ F k hF) =
      @moduleCycle S B X _ _ pX _ _ δ _
        ((Modules.pullback f).obj F)
        (@Modules.instIsCoherent_pullback S X Y
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (LocallyOfFiniteType.isLocallyNoetherian pY) f F _)
        (k + (r : ℤ))
        (moduleSupportDeltaDimension_pullback_le pY pX δ f r hf k F hF) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
