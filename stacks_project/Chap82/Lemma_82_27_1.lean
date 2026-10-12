/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern

/-!
# Projective bundle Chern-power pushforward

In Situation 82.2.1, the associated projective bundle of a finite locally free
module of rank `r = q + 1` has the displayed identities for
`π_* (c₁(𝒪_P(1))^s ∩ π^* α)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
namespace HigherChern

section PushforwardC1PowerCap
variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- Proper pushforward of a power of `c₁(𝒪_P(1))` capped with the pullback along
the associated projective bundle `π : P(E) ⟶ X`. For rank `r = q + 1` the
output lives in `CH_{k + q - s}(X)`, matching `CH_{k + r - 1 - s}(X)`. -/
def pushforwardC1PowerCap (k : ℤ) (s : ℕ) :
    Hom.chowGroup f δ k →+ Hom.chowGroup f δ (k + q - s) :=
  let π := ProjectiveAtlas.projection E
  let H := TautologicalDescent.O1 E
  (properPushforward δ (π ≫ f) f π rfl (k + q - s)).comp
    ((FirstChernChow.power (π ≫ f) δ H s (k + q)).comp
      (ProjectiveFormulaMap.pullback f δ π q k))

/-- Evaluating `pushforwardC1PowerCap` is the displayed composite
`π_* ∘ (c₁(𝒪_P(1))^s ∩ -) ∘ π^*`. -/
theorem pushforwardC1PowerCap_apply (k : ℤ) (s : ℕ)
    (α : Hom.chowGroup f δ k) :
    pushforwardC1PowerCap f δ E q k s α =
      properPushforward δ (ProjectiveAtlas.projection E ≫ f) f
        (ProjectiveAtlas.projection E) rfl (k + q - s)
        (FirstChernChow.power (ProjectiveAtlas.projection E ≫ f) δ
          (TautologicalDescent.O1 E) s (k + q)
          (ProjectiveFormulaMap.pullback f δ (ProjectiveAtlas.projection E) q k α)) := sorry

/-- The top-degree case `s = q` of `pushforwardC1PowerCap`, reindexed to
`CH_k(X)` along `k + q - q = k`. -/
def pushforwardTopC1PowerCap (k : ℤ) :
    Hom.chowGroup f δ k →+ Hom.chowGroup f δ k :=
  (ChowCohomology.castChowGroup δ f (add_sub_cancel_right k (q : ℤ))).comp
    (pushforwardC1PowerCap f δ E q k q)

/-- Evaluating `pushforwardTopC1PowerCap` is `pushforwardC1PowerCap` in degree
`q`, followed by canonical degree transport. -/
theorem pushforwardTopC1PowerCap_apply (k : ℤ) (α : Hom.chowGroup f δ k) :
    pushforwardTopC1PowerCap f δ E q k α =
      ChowCohomology.castChowGroup δ f (add_sub_cancel_right k (q : ℤ))
        (pushforwardC1PowerCap f δ E q k q α) := sorry

end PushforwardC1PowerCap

/-- Lemma 82.27.1 (1): In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r = q + 1`, and let
`(π : P ⟶ X, 𝒪_P(1))` be the associated projective bundle. For any
`α ∈ CH_k(X)` and `s < r - 1` (equivalently `s < q`), the class
`π_* (c₁(𝒪_P(1))^s ∩ π^* α)` vanishes in `CH_{k + r - 1 - s}(X)`. -/
@[stacks 0ERU]
theorem pushforwardC1PowerCap_eq_zero_of_lt
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (k : ℤ) (s : ℕ) (hs : s < q) (α : Hom.chowGroup f δ k) :
    pushforwardC1PowerCap f δ E q k s α = 0 := sorry

/-- Lemma 82.27.1 (2): In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r = q + 1`, and let
`(π : P ⟶ X, 𝒪_P(1))` be the associated projective bundle. For any
`α ∈ CH_k(X)` the class `π_* (c₁(𝒪_P(1))^(r - 1) ∩ π^* α)` equals `α` in
`CH_k(X)`. -/
@[stacks 0ERU]
theorem pushforwardTopC1PowerCap_eq_self
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (k : ℤ) (α : Hom.chowGroup f δ k) :
    pushforwardTopC1PowerCap f δ E q k α = α := sorry

end HigherChern
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
