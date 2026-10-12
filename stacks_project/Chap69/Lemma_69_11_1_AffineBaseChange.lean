/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»

/-!
# Affine pushforward, vanishing, and cartesian base change

Along an affine morphism of algebraic spaces, pushforward of a quasi-coherent module remains
quasi-coherent, higher direct images vanish in positive degree, and underived pushforward
commutes with arbitrary cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace pushforward

/-- Module pushforward along a morphism of algebraic spaces is a right adjoint, hence left
exact. -/
instance isRightAdjoint (f : X ⟶ Y) : (pushforward f).IsRightAdjoint :=
  (pullbackPushforwardAdjunction f).isRightAdjoint

/-- Pushforward of a quasi-coherent module along an affine morphism of algebraic spaces is
quasi-coherent. -/
instance isQuasicoherent (f : X ⟶ Y) [Affine f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((pushforward f).obj ℱ).IsQuasicoherent :=
  sorry

/-- Explicit-hypothesis form of affine pushforward preserving quasi-coherence. -/
theorem isQuasicoherentOf (f : X ⟶ Y) [Affine f] {ℱ : X.Modules}
    (hℱ : ℱ.IsQuasicoherent) : ((pushforward f).obj ℱ).IsQuasicoherent :=
  sorry

end pushforward

/-- Positive-degree higher direct images of a quasi-coherent module along an affine morphism of
algebraic spaces vanish. -/
theorem higherDirectImage_isZero_of_affine (f : X ⟶ Y) [Affine f]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) (hi : 0 < i) :
    IsZero (higherDirectImage f ℱ i) :=
  sorry

/-- Pushforward of a quasi-coherent module along an affine morphism of algebraic spaces commutes
with arbitrary cartesian base change. -/
theorem affineBaseChange_pushforward_isomorphic {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_cart : IsPullback g' f' f g) [Affine f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic ((pullback g).obj ((pushforward f).obj ℱ))
      ((pushforward f').obj ((pullback g').obj ℱ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
