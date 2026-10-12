/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap67.«67_11_1_1_Comparison»
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Representable pushforward of quasi-coherent modules

For a representable quasi-compact quasi-separated morphism of algebraic spaces, restriction of
`f_* F` to an étale scheme atlas of the target agrees with pushforward of the restricted module
along the base-changed morphism of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism from a represented scheme into an algebraic space, rewritten as a morphism of
algebraic spaces from `ofOver T`. -/
def homOfYoneda {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (φ : yoneda.obj T ⟶ X.functorOfPoints) : ofOver T ⟶ X :=
  φ

/-- A morphism of algebraic spaces from `ofOver T` as a map of functors of points from
`yoneda.obj T`. -/
def yonedaHomOf {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (φ : ofOver T ⟶ X) : yoneda.obj T ⟶ X.functorOfPoints :=
  φ

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The projection `U ⟶ X` of the represented pullback of `f` along a morphism from a scheme. -/
def representablePullbackFst {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {V : Over S} (g : ofOver V ⟶ Y) : ofOver (hf.pullback (yonedaHomOf g)) ⟶ X :=
  homOfYoneda (hf.fst (yonedaHomOf g))

/-- The projection `U ⟶ V` of the represented pullback of `f` along a morphism from a scheme. -/
def representablePullbackSnd {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {V : Over S} (g : ofOver V ⟶ Y) :
    ofOver (hf.pullback (yonedaHomOf g)) ⟶ ofOver V :=
  ofOverMap (hf.snd (yonedaHomOf g))

/-- The represented pullback square of a representable morphism along a morphism from a scheme. -/
theorem representablePullback_isPullback {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {V : Over S} (g : ofOver V ⟶ Y) :
    IsPullback (representablePullbackFst hf g) (representablePullbackSnd hf g) f g :=
  sorry

/-- 67.11.1.1: Let `f : X ⟶ Y` be a representable, quasi-compact, and quasi-separated morphism of
algebraic spaces over `S`. Let `V` be a scheme and `V ⟶ Y` an étale surjective morphism, write
`U = V ×_Y X` with base change `f' : U ⟶ V`. Then for any quasi-coherent `𝒪_X`-module `F` there
is a canonical identification `f'_*(F|_U) ≅ (f_* F)|_V` of sheaves of modules on `V_étale`. -/
@[stacks 04CF]
def representablePushforwardIso {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g] [Etale (representablePullbackFst hf g)]
    (F : X.Modules) [F.IsQuasicoherent] :
    (restrictFunctor g).obj ((pushforward f).obj F) ≅
      (pushforward (representablePullbackSnd hf g)).obj
        (restrict F (representablePullbackFst hf g)) :=
  pushforwardEtaleBaseChangeIso (representablePullback_isPullback hf g) F

/-- The source-facing identification is the general étale cartesian comparison at the represented
pullback square of `f` along `g`. -/
theorem representablePushforwardIso_eq {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g] [Etale (representablePullbackFst hf g)]
    (F : X.Modules) [F.IsQuasicoherent] :
    representablePushforwardIso hf g F =
      pushforwardEtaleBaseChangeIso (representablePullback_isPullback hf g) F :=
  rfl

/-- Both sides of the source identification are étale restriction and module pushforward of `F`. -/
theorem representablePushforwardIso_spec {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g] [Etale (representablePullbackFst hf g)]
    (F : X.Modules) [F.IsQuasicoherent] :
    (representablePushforwardIso hf g F).hom =
      pushforwardEtaleBaseChangeHom (representablePullback_isPullback hf g) F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
