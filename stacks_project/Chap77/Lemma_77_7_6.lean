/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_20_6
public import stacks_project.Chap69.Lemma_69_11_1_AffineBaseChange
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Lemma 77.7.6

In Situation 77.7.1, an affine morphism `i : Z ⟶ X` with `𝒢 = i_* ℋ` identifies the
vanishing flattening functors of `u` and of its adjoint `v`; if `i` is a closed
immersion, the same holds for the surjectivity functors.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
variable {ℱ : X.Modules} {ℋ : Z.Modules}

/-- The morphism `v : i^* ℱ ⟶ ℋ` adjoint to `u : ℱ ⟶ i_* ℋ` under
`pullbackPushforwardAdjunction i`. -/
def adjointToPushforward (u : ℱ ⟶ (pushforward i).obj ℋ) :
    (pullback i).obj ℱ ⟶ ℋ :=
  ((pullbackPushforwardAdjunction i).homEquiv ℱ ℋ).symm u

/-- `adjointToPushforward i u` is the inverse image of `u` under the Hom-equivalence of
`pullbackPushforwardAdjunction i`. -/
theorem adjointToPushforward_eq (u : ℱ ⟶ (pushforward i).obj ℋ) :
    adjointToPushforward i u = ((pullbackPushforwardAdjunction i).homEquiv ℱ ℋ).symm u :=
  sorry

/-- The adjunction Hom-equivalence sends `adjointToPushforward i u` back to `u`. -/
theorem homEquiv_adjointToPushforward (u : ℱ ⟶ (pushforward i).obj ℋ) :
    (pullbackPushforwardAdjunction i).homEquiv ℱ ℋ (adjointToPushforward i u) = u :=
  sorry

variable {B : AlgebraicSpace S} (f : X ⟶ B)
variable [ℱ.IsQuasicoherent] [ℋ.IsQuasicoherent]
variable (u : ℱ ⟶ (pushforward i).obj ℋ)

/-- Lemma 77.7.6 (1): In Situation 77.7.1, given an affine morphism `i : Z ⟶ X` and a
quasi-coherent `𝒪_Z`-module `ℋ` with `𝒢 = i_* ℋ`, if `v : i^* ℱ ⟶ ℋ` is adjoint to
`u : ℱ ⟶ 𝒢`, then `F_{v, zero} = F_{u, zero}`: for every scheme `T` over `B`,
`baseChangeMap f T.hom u = 0` if and only if
`baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u) = 0`. -/
@[stacks 0CW7]
theorem baseChangeMap_zero_iff_adjoint [Affine i] (T : SchemeOver B) :
    baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u) = 0 :=
  sorry

/-- Lemma 77.7.6 (2): In Situation 77.7.1, if moreover `i` is a closed immersion, then
`F_{v, surj} = F_{u, surj}`: for every scheme `T` over `B`,
`Epi (baseChangeMap f T.hom u)` if and only if
`Epi (baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u))`. -/
@[stacks 0CW7]
theorem baseChangeMap_epi_iff_adjoint [IsClosedImmersion i] (T : SchemeOver B) :
    Epi (baseChangeMap f T.hom u) ↔
      Epi (baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
