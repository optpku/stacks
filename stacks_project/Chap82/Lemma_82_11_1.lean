/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_11_1_Pullback
public import stacks_project.Chap82.Lemma_82_8_2_Pushforward

/-!
# Cartesian compatibility of proper pushforward and flat pullback

In Situation 82.2.1, a cartesian square of good algebraic spaces over `B`
preserves properness and flatness of exact relative dimension, and the
induced cycle operations satisfy `g^* ∘ f_* = f'_* ∘ (g')^*`.

The flat pullback on cycle groups is the import-isolated operator
`cycleFlatPullback`, definitionally `flatPullbackHom`, because
`Lemma_82_10_4_Pullback` cannot be imported beside
`Lemma_82_8_2_Pushforward`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 82.11.1 (1): In Situation 82.2.1, let
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` be a fibre product
diagram of good algebraic spaces over `B`. If `f` is proper, then `f'` is
proper. -/
@[stacks 0EPD]
theorem proper_of_isPullback {S : Scheme.{u}} {B X Y X' Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiSeparated (g' ≫ pX)] [LocallyOfFiniteType (g' ≫ pX)]
    (square : IsPullback g' f' f g) [Proper f]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : f' ≫ pY' = g' ≫ pX) : Proper f' :=
  sorry

/-- Lemma 82.11.1 (2): In Situation 82.2.1, let
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` be a fibre product
diagram of good algebraic spaces over `B`. If `g` is flat, then `g'` is
flat. -/
@[stacks 0EPD]
theorem flat_of_isPullback {S : Scheme.{u}} {B X Y X' Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiSeparated (g' ≫ pX)] [LocallyOfFiniteType (g' ≫ pX)]
    (square : IsPullback g' f' f g) [Flat g]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : f' ≫ pY' = g' ≫ pX) : Flat g' :=
  sorry

/-- Lemma 82.11.1 (3): In Situation 82.2.1, let
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` be a fibre product
diagram of good algebraic spaces over `B`. If `g` is of relative dimension
`r`, then `g'` is of relative dimension `r`. -/
@[stacks 0EPD]
theorem relativeDimension_of_isPullback {S : Scheme.{u}}
    {B X Y X' Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiSeparated (g' ≫ pX)] [LocallyOfFiniteType (g' ≫ pX)]
    (square : IsPullback g' f' f g) (r : ℕ) [RelativeDimension g r]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : f' ≫ pY' = g' ≫ pX) : RelativeDimension g' r :=
  sorry

/-- Lemma 82.11.1 (4): In Situation 82.2.1, let
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` be a fibre product
diagram of good algebraic spaces over `B`. If `f` is proper and `g` is flat of
relative dimension `r`, then `g^* ∘ f_* = f'_* ∘ (g')^*` as maps
`Z_k(X) →+ Z_{k + r}(Y')`. -/
@[stacks 0EPD]
theorem flatPullbackHom_comp_properPushforwardHom {S : Scheme.{u}}
    {B X Y X' Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiSeparated (g' ≫ pX)] [LocallyOfFiniteType (g' ≫ pX)]
    (square : IsPullback g' f' f g) (r : ℕ)
    [Proper f] [Flat g] [RelativeDimension g r]
    [Proper f'] [Flat g'] [RelativeDimension g' r]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : f' ≫ pY' = g' ≫ pX) (k : ℤ) :
    (cycleFlatPullback pY pY' δ g r hg k).comp
        (properPushforwardHom pX pY δ f hf k) =
      (properPushforwardHom (g' ≫ pX) pY' δ f' hf' (k + (r : ℤ))).comp
        (cycleFlatPullback pX (g' ≫ pX) δ g' r rfl k) :=
  sorry

/-- Evaluation of `flatPullbackHom_comp_properPushforwardHom` on a single
`k`-cycle of `X`. -/
theorem flatPullbackHom_comp_properPushforwardHom_apply {S : Scheme.{u}}
    {B X Y X' Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiSeparated (g' ≫ pX)] [LocallyOfFiniteType (g' ≫ pX)]
    (square : IsPullback g' f' f g) (r : ℕ)
    [Proper f] [Flat g] [RelativeDimension g r]
    [Proper f'] [Flat g'] [RelativeDimension g' r]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : f' ≫ pY' = g' ≫ pX) (k : ℤ) (α : (cycleGroup pX) δ k) :
    cycleFlatPullback pY pY' δ g r hg k
        (properPushforwardHom pX pY δ f hf k α) =
      properPushforwardHom (g' ≫ pX) pY' δ f' hf' (k + (r : ℤ))
        (cycleFlatPullback pX (g' ≫ pX) δ g' r rfl k α) :=
  sorry

/-- Specialization of `flatPullbackHom_comp_properPushforwardHom` to the
chosen fibre product of `f` and `g`. -/
theorem flatPullbackHom_comp_properPushforwardHom_pullback {S : Scheme.{u}}
    {B X Y Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (r : ℕ)
    [Proper f] [Flat g] [RelativeDimension g r] [HasPullback f g]
    [QuasiSeparated (pullback.fst f g ≫ pX)]
    [LocallyOfFiniteType (pullback.fst f g ≫ pX)]
    [Proper (pullback.snd f g)] [Flat (pullback.fst f g)]
    [RelativeDimension (pullback.fst f g) r]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : pullback.snd f g ≫ pY' = pullback.fst f g ≫ pX) (k : ℤ) :
    (cycleFlatPullback pY pY' δ g r hg k).comp
        (properPushforwardHom pX pY δ f hf k) =
      (properPushforwardHom (pullback.fst f g ≫ pX) pY' δ
          (pullback.snd f g) hf' (k + (r : ℤ))).comp
        (cycleFlatPullback pX (pullback.fst f g ≫ pX) δ
          (pullback.fst f g) r rfl k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
