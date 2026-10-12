/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_8_2_Pushforward
public import stacks_project.Chap82.Lemma_82_6_3
public import stacks_project.Chap76.Lemma_76_42_10_Pushforward

/-!
# Proper pushforward of associated cycles

In Situation 82.2.1, proper pushforward of the degree-`k` cycle of a closed
subspace (resp. a coherent sheaf) agrees with the degree-`k` associated cycle
of the ordinary pushforward sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The `δ`-dimension of the support of `f_* F` is at most `k` whenever
`dim_δ(Supp(F)) ≤ k`, for a proper morphism of good algebraic spaces over `B`. -/
theorem moduleSupportDeltaDimension_pushforward_le
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pX δ F ≤ (k : EInt)) :
    @moduleSupportDeltaDimension S B Y _ _ pY _ _ δ _
        ((Modules.pushforward f).obj F)
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY) F _) ≤
      (k : EInt) :=
  sorry

/-- The `δ`-dimension of the support of `f_*(i_* 𝒪_Z)` is at most `k` whenever
`dim_δ(Z) ≤ k`, for a proper morphism of good algebraic spaces over `B`. -/
theorem moduleSupportDeltaDimension_pushforward_closedSubspace_le
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (Z : ClosedSubspace X)
    (hZ : closedSubspaceDeltaDimension pX δ Z ≤ (k : EInt)) :
    @moduleSupportDeltaDimension S B Y _ _ pY _ _ δ _
        ((Modules.pushforward f).obj
          ((Modules.pushforward Z.ι).obj
            (SheafOfModules.unit (structureSheaf Z.X))))
        (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
          (LocallyOfFiniteType.isLocallyNoetherian pY)
          ((Modules.pushforward Z.ι).obj
            (SheafOfModules.unit (structureSheaf Z.X)))
          (@instIsCoherent_pushforward_unit S X
            (LocallyOfFiniteType.isLocallyNoetherian pX) Z)) ≤
      (k : EInt) :=
  sorry

/-- Lemma 82.8.3 (1): In Situation 82.2.1 let `f : X ⟶ Y` be a proper morphism of
good algebraic spaces over `B`. If `Z ⊂ X` is a closed subspace with
`dim_δ(Z) ≤ k`, then `f_*[Z]_k = [f_* 𝒪_Z]_k`. Note that `f_* 𝒪_Z` is coherent
by Cohomology of Spaces, Lemma 69.20.2. -/
@[stacks 0EP3]
theorem properPushforward_closedSubspaceCycle
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (Z : ClosedSubspace X)
    (hZ : closedSubspaceDeltaDimension pX δ Z ≤ (k : EInt)) :
    properPushforwardCycle pX pY δ f hf
        (@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian pX) Z
          (relativeDimensionFunction pX δ) k) =
      @moduleCycle S B Y _ _ pY _ _ δ _
          ((Modules.pushforward f).obj
            ((Modules.pushforward Z.ι).obj
              (SheafOfModules.unit (structureSheaf Z.X))))
          (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
            (LocallyOfFiniteType.isLocallyNoetherian pY)
            ((Modules.pushforward Z.ι).obj
              (SheafOfModules.unit (structureSheaf Z.X)))
            (@instIsCoherent_pushforward_unit S X
              (LocallyOfFiniteType.isLocallyNoetherian pX) Z))
          k
          (moduleSupportDeltaDimension_pushforward_closedSubspace_le
            pX pY δ f hf k Z hZ) :=
  sorry

/-- Lemma 82.8.3 (2): In Situation 82.2.1 let `f : X ⟶ Y` be a proper morphism of
good algebraic spaces over `B`. If `F` is a coherent `𝒪_X`-module with
`dim_δ(Supp(F)) ≤ k`, then `f_*[F]_k = [f_* F]_k`. Note that `f_* F` is coherent
by Cohomology of Spaces, Lemma 69.20.2. -/
@[stacks 0EP3]
theorem properPushforward_moduleCycle
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)
    (F : X.Modules) [F.IsCoherent]
    (hF : moduleSupportDeltaDimension pX δ F ≤ (k : EInt)) :
    properPushforwardCycle pX pY δ f hf (moduleCycle pX δ F k hF) =
      @moduleCycle S B Y _ _ pY _ _ δ _
          ((Modules.pushforward f).obj F)
          (@Modules.pushforward_obj_isCoherent_of_proper S X Y f _
            (LocallyOfFiniteType.isLocallyNoetherian pY) F _)
          k
          (moduleSupportDeltaDimension_pushforward_le pX pY δ f hf k F hF) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
