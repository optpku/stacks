/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_4_Locus

/-!
# Open locus where derived pushforward is a vector bundle of fixed rank and degree

For a proper, flat, finitely presented morphism of algebraic spaces and a finitely
presented module flat over the target, the locus in the target where the base-changed
derived pushforward is a finite locally free module of rank `r` placed in degree `i`
is an open subspace.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The derived pushforward `Rf_{T,*} F_T` obtained by pulling `F` back along the projection
`X ×_Y T ⟶ X`, placing the result in degree `0`, and pushing forward along `X ×_Y T ⟶ T`. -/
abbrev baseChangeDerivedPushforward {T : AlgebraicSpace S} (f : X ⟶ Y) (g : T ⟶ Y)
    (F : X.Modules) : ModuleDerived T :=
  (Modules.pushforwardDerived (Limits.pullback.snd f g)).obj
    ((DerivedCategory.singleFunctor (Modules (Limits.pullback f g)) 0).obj
      ((Modules.pullback (Limits.pullback.fst f g)).obj F))

/-- Unfolding of `baseChangeDerivedPushforward` as derived pushforward of the degree-`0`
placement of the ordinary pullback `F_T`. -/
theorem baseChangeDerivedPushforward_eq {T : AlgebraicSpace S} (f : X ⟶ Y) (g : T ⟶ Y)
    (F : X.Modules) :
    baseChangeDerivedPushforward f g F =
      (Modules.pushforwardDerived (Limits.pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor (Modules (Limits.pullback f g)) 0).obj
          ((Modules.pullback (Limits.pullback.fst f g)).obj F)) :=
  sorry

/-- Along a proper morphism of finite presentation, derived pushforward of a finitely
presented module flat over the target is perfect. -/
theorem isPerfect_pushforwardDerived_single (f : X ⟶ Y) [Proper f] [FinitePresentation f]
    (F : X.Modules) (hF_fp : F.IsFinitePresentation) (hF_flat : Modules.flatOver F f) :
    IsPerfect
      ((Modules.pushforwardDerived f).obj
        ((DerivedCategory.singleFunctor (Modules X) 0).obj F)) :=
  sorry

/-- The canonical open subspace of `Y` on which `Rf_* F` is a vector bundle of rank `r`
placed in degree `i`, for a finitely presented `𝒪_X`-module `F` that is flat over `Y`. -/
def pushforwardVectorBundleLocus (f : X ⟶ Y) [Proper f] [FinitePresentation f]
    (F : X.Modules) (hF_fp : F.IsFinitePresentation) (hF_flat : Modules.flatOver F f)
    (i r : ℤ) : OpenSubspace Y :=
  IsPerfect.vectorBundleLocus (isPerfect_pushforwardDerived_single f F hF_fp hF_flat) i r

/-- The geometric vector-bundle locus of `Rf_* F` is the vector-bundle locus of the
perfect derived pushforward. -/
theorem pushforwardVectorBundleLocus_eq (f : X ⟶ Y) [Proper f] [FinitePresentation f]
    (F : X.Modules) (hF_fp : F.IsFinitePresentation) (hF_flat : Modules.flatOver F f)
    (i r : ℤ) :
    pushforwardVectorBundleLocus f F hF_fp hF_flat i r =
      IsPerfect.vectorBundleLocus (isPerfect_pushforwardDerived_single f F hF_fp hF_flat) i r :=
  sorry

/-- Lemma 75.26.5: let `S` be a scheme and let `f : X ⟶ Y` be a proper, flat, finitely
presented morphism of algebraic spaces over `S`. Let `F` be an `𝒪_X`-module of finite
presentation, flat over `Y`. Fix `i, r : ℤ` with `0 ≤ r`. Then a morphism `g : T ⟶ Y`
factors through `pushforwardVectorBundleLocus f F hF_fp hF_flat i r` if and only if
`baseChangeDerivedPushforward f g F` is a finite locally free module of rank `r` placed
in degree `i`. -/
@[stacks 0E6A]
theorem pushforwardVectorBundleLocus_factor_iff
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (F : X.Modules) (hF_fp : F.IsFinitePresentation) (hF_flat : Modules.flatOver F f)
    (i r : ℤ) (hr : 0 ≤ r) {T : AlgebraicSpace S} (g : T ⟶ Y) :
    (∃ lift : T ⟶ (pushforwardVectorBundleLocus f F hF_fp hF_flat i r).X,
        lift ≫ (pushforwardVectorBundleLocus f F hF_fp hF_flat i r).ι = g) ↔
      IsVectorBundleOfRankInDegree (baseChangeDerivedPushforward f g F) i r :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
