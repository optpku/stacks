/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.Lemma_69_11_1_AffineBaseChange
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Lemma 77.7.7

In Situation 77.7.1, an affine morphism `g : X ⟶ X'` over `B` does not change the
flattening functors of `u` on `Sch/B`: the functors for `u` agree with those for
`(pushforward g).map u`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X' ⟶ B) (g : X ⟶ X') [Affine g]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- Lemma 77.7.7 (1): In Situation 77.7.1, if `g : X ⟶ X'` is affine, then
`IsIso (baseChangeMap (g ≫ f) T.hom u)` if and only if
`IsIso (baseChangeMap f T.hom ((pushforward g).map u))`. This is the equality
`F_iso = F'_iso` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 0CW8]
theorem baseChangeMap_isIso_iff_of_affine_pushforward (T : SchemeOver B) :
    IsIso (baseChangeMap (g ≫ f) T.hom u) ↔
      IsIso (baseChangeMap f T.hom ((pushforward g).map u)) :=
  sorry

/-- Lemma 77.7.7 (2): In Situation 77.7.1, if `g : X ⟶ X'` is affine, then
`Mono (baseChangeMap (g ≫ f) T.hom u)` if and only if
`Mono (baseChangeMap f T.hom ((pushforward g).map u))`. This is the equality
`F_inj = F'_inj` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 0CW8]
theorem baseChangeMap_mono_iff_of_affine_pushforward (T : SchemeOver B) :
    Mono (baseChangeMap (g ≫ f) T.hom u) ↔
      Mono (baseChangeMap f T.hom ((pushforward g).map u)) :=
  sorry

/-- Lemma 77.7.7 (3): In Situation 77.7.1, if `g : X ⟶ X'` is affine, then
`Epi (baseChangeMap (g ≫ f) T.hom u)` if and only if
`Epi (baseChangeMap f T.hom ((pushforward g).map u))`. This is the equality
`F_surj = F'_surj` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 0CW8]
theorem baseChangeMap_epi_iff_of_affine_pushforward (T : SchemeOver B) :
    Epi (baseChangeMap (g ≫ f) T.hom u) ↔
      Epi (baseChangeMap f T.hom ((pushforward g).map u)) :=
  sorry

/-- Lemma 77.7.7 (4): In Situation 77.7.1, if `g : X ⟶ X'` is affine, then
`baseChangeMap (g ≫ f) T.hom u = 0` if and only if
`baseChangeMap f T.hom ((pushforward g).map u) = 0`. This is the equality
`F_zero = F'_zero` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 0CW8]
theorem baseChangeMap_zero_iff_of_affine_pushforward (T : SchemeOver B) :
    baseChangeMap (g ≫ f) T.hom u = 0 ↔
      baseChangeMap f T.hom ((pushforward g).map u) = 0 :=
  sorry

/-- Pointwise, `isomorphismFunctor (g ≫ f) u` and
`isomorphismFunctor f ((pushforward g).map u)` are nonempty on the same objects of
`SchemeOver B`. -/
theorem isomorphismFunctor_obj_nonempty_iff_of_affine_pushforward (T : SchemeOver B) :
    Nonempty ((isomorphismFunctor (g ≫ f) u).obj (op T)) ↔
      Nonempty ((isomorphismFunctor f ((pushforward g).map u)).obj (op T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
