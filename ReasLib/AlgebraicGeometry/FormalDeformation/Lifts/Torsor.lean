/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Tangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.SquareZero
public import ReasLib.AlgebraicGeometry.FormalDeformation.SelfPullbackLifts
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger

/-!
# Tangent tensor actions and torsors on deformation lifts

For a surjection with maximal-ideal-annihilated kernel, the self-pullback
comparison defines an action and a difference on lift classes. The acting
module is the residue-slice tangent space tensored with the kernel.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat IsLocalRing
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable {A' A : ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- The square-zero pullback comparison of lift classes as an equivalence. -/
def liftsSquareZeroPullbackEquiv [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    lifts p (squareZeroPullbackToBase A' (kerModule f hI) f) x ≃
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 :=
  Equiv.ofBijective (liftsSquareZeroPullback f hf hI x φ)
    (liftsSquareZeroPullback_bijective f hf hI x φ)

/-- The underlying function of `liftsSquareZeroPullbackEquiv` is
`liftsSquareZeroPullback`. -/
theorem liftsSquareZeroPullbackEquiv_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    (liftsSquareZeroPullbackEquiv f hf hI x φ).toFun =
      liftsSquareZeroPullback f hf hI x φ := rfl

/-- The first component of `liftsSquareZeroPullbackEquiv` is pushforward along the
first projection of `A' ×_k k[I]`. -/
theorem liftsSquareZeroPullbackEquiv_fst [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' (kerModule f hI) f) x) :
    (liftsSquareZeroPullbackEquiv f hf hI x φ (Quotient.mk'' a)).1 =
      Quotient.mk''
        (ObjectLift.pushforwardAlong (squareZeroPullbackFst A' (kerModule f hI)) f a) :=
  liftsSquareZeroPullback_fst f hf hI x φ a

/-- The second component of `liftsSquareZeroPullbackEquiv` is pushforward along the
second projection of `A' ×_k k[I]`, after composing with the chosen residue
pushforward. -/
theorem liftsSquareZeroPullbackEquiv_snd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' (kerModule f hI) f) x) :
    (liftsSquareZeroPullbackEquiv f hf hI x φ (Quotient.mk'' a)).2 =
      Quotient.mk''
        (ObjectLift.pushforwardAlong (squareZeroPullbackSnd A' (kerModule f hI))
          (squareZeroToResidue Λ k (kerModule f hI))
          (ObjectLift.compSquareZeroResidue φ a)) :=
  liftsSquareZeroPullback_snd f hf hI x φ a

/-- The self-pullback pairing and residue-plus-difference comparison identify pairs of lifts
with a lift and a square-zero residue lift. -/
def liftsPairEquiv [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    lifts p f x × lifts p f x ≃
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 :=
  (@liftsSelfPullbackEquiv Λ k _ _ _ _ _ F _ p A A'
    IsDeformationCategory.hasRimSchlessinger f hf x).trans
    ((liftsSelfPullbackIsoEquiv f hf hI x).trans
      (liftsSquareZeroPullbackEquiv f hf hI x φ))

/-- The lift-pair comparison preserves the first lift. -/
theorem liftsPairEquiv_fst [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x1 x2 : lifts p f x) :
    (liftsPairEquiv f hf hI x φ (x1, x2)).1 = x1 := sorry

/-- The inverse lift-pair comparison preserves the first lift. -/
theorem liftsPairEquiv_symm_fst [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x' : lifts p f x)
    (θ : lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0) :
    ((liftsPairEquiv f hf hI x φ).symm (x', θ)).1 = x' := sorry

/-- Construction-level action of `Lift(x0, k[I])` on `Lift(x, A')`. -/
def liftsVAdd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0)
    (x' : lifts p f x) : lifts p f x :=
  ((liftsPairEquiv f hf hI x φ).symm (x', θ)).2

/-- Construction-level difference of two lifts of `x` along `f`. -/
def liftsVSub [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x'' x' : lifts p f x) :
    lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 :=
  (liftsPairEquiv f hf hI x φ (x', x'')).2

/-- `liftsVAdd θ x'` is the unique lift whose pairing with `x'` recovers `θ`. -/
theorem liftsVAdd_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0)
    (x' : lifts p f x) :
    liftsPairEquiv f hf hI x φ (x', liftsVAdd f hf hI x φ θ x') = (x', θ) := sorry

/-- `liftsVSub x'' x'` is the second component of Φ on the ordered pair `(x', x'')`. -/
theorem liftsVSub_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x'' x' : lifts p f x) :
    liftsVSub f hf hI x φ x'' x' = (liftsPairEquiv f hf hI x φ (x', x'')).2 := rfl

/-- The slice tangent tensor `T F_x0 ⊗[k] I` for `I = kerModule f hI`. -/
abbrev tangentTensor [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :=
  (fiberIsoClassFunctor (Over.forget (fiberInclusion.obj x0) ⋙ p)).obj (dualNumber Λ k) ⊗[k]
    kerModule f hI

/-- Additive group structure on `Lift(x0, k[I])`, transported from the bundled
`FGModuleCat` identification. -/
instance instAddCommGroup_lifts_kerModule [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    AddCommGroup (lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0) :=
  instAddCommGroup_liftsSquareZero p x0 (FGModuleCat.of k (kerModule f hI))

/-- `k`-module structure on `Lift(x0, k[I])`, transported from the bundled
`FGModuleCat` identification. -/
instance instModule_lifts_kerModule [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    Module k (lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0) :=
  instModule_liftsSquareZero p x0 (FGModuleCat.of k (kerModule f hI))

/-- Square-zero residue lifts identify linearly with the residue-slice tangent tensor. -/
abbrev liftsTangentTensorEquiv [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 ≃ₗ[k] tangentTensor f hI x0 :=
  @liftsSquareZeroLinearEquiv Λ k _ _ _ _ _ F _ p _ x0
    (FGModuleCat.of k (kerModule f hI))
    (@HasRimSchlessinger.toHasSchlessingerS2 Λ k _ _ _ _ _ F _ p
      IsDeformationCategory.hasRimSchlessinger)

/-- `liftsTangentTensorEquiv` is `liftsSquareZeroLinearEquiv` at `kerModule f hI`. -/
theorem liftsTangentTensorEquiv_spec [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    liftsTangentTensorEquiv f hI x0 =
      @liftsSquareZeroLinearEquiv Λ k _ _ _ _ _ F _ p _ x0
    (FGModuleCat.of k (kerModule f hI))
    (@HasRimSchlessinger.toHasSchlessingerS2 Λ k _ _ _ _ _ F _ p
      IsDeformationCategory.hasRimSchlessinger) := rfl

/-- Action of `T F_x0 ⊗[k] I` on `Lift(x, A')`, transported from `liftsVAdd`. -/
def liftsTensorVAdd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x) : lifts p f x :=
  liftsVAdd f hf hI x φ ((liftsTangentTensorEquiv f hI x0).symm θ) x'

/-- Difference of two lifts, as an element of `T F_x0 ⊗[k] I`. -/
def liftsTensorVSub [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x'' x' : lifts p f x) : tangentTensor f hI x0 :=
  liftsTangentTensorEquiv f hI x0 (liftsVSub f hf hI x φ x'' x')

/-- Tensor-space addition is construction-level addition after applying the inverse
of `liftsTangentTensorEquiv`. -/
theorem liftsTensorVAdd_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x) :
    liftsTensorVAdd f hf hI x φ θ x' =
      liftsVAdd f hf hI x φ ((liftsTangentTensorEquiv f hI x0).symm θ) x' := rfl

/-- Tensor-space subtraction is construction-level subtraction, transported by
`liftsTangentTensorEquiv`. -/
theorem liftsTensorVSub_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x'' x' : lifts p f x) :
    liftsTensorVSub f hf hI x φ x'' x' =
      liftsTangentTensorEquiv f hI x0 (liftsVSub f hf hI x φ x'' x') := rfl

/-- The tangent tensor acts additively on lifts. -/
theorem liftsTensorVAdd_add [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ η : tangentTensor f hI x0) (x' : lifts p f x) :
    liftsTensorVAdd f hf hI x φ (θ + η) x' =
      liftsTensorVAdd f hf hI x φ θ (liftsTensorVAdd f hf hI x φ η x') := sorry

/-- The zero tangent tensor fixes every lift. -/
theorem liftsTensorVAdd_zero [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x' : lifts p f x) :
    liftsTensorVAdd f hf hI x φ 0 x' = x' := sorry

/-- Adding the tensor difference to its base lift recovers the other lift. -/
theorem liftsTensorVSub_vadd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x'' x' : lifts p f x) :
    liftsTensorVAdd f hf hI x φ (liftsTensorVSub f hf hI x φ x'' x') x' = x'' := sorry

/-- The tensor difference of a translated lift and its base is the translating tensor. -/
theorem liftsTensorVAdd_vsub [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x) :
    liftsTensorVSub f hf hI x φ (liftsTensorVAdd f hf hI x φ θ x') x' = θ := sorry

/-- The additive action of `T F_x0 ⊗[k] I` on `Lift(x, A')`. -/
@[reducible]
def liftsAddAction [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    AddAction (tangentTensor f hI x0) (lifts p f x) where
  vadd := liftsTensorVAdd f hf hI x φ
  add_vadd := liftsTensorVAdd_add f hf hI x φ
  zero_vadd := liftsTensorVAdd_zero f hf hI x φ

/-- `liftsAddAction` acts by `liftsTensorVAdd`. -/
theorem liftsAddAction_vadd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x) :
    (liftsAddAction f hf hI x φ).vadd θ x' =
      liftsTensorVAdd f hf hI x φ θ x' := rfl

/-- If `Lift(x, A')` is nonempty, then `T F_x0 ⊗[k] I` acts freely and transitively
on it. -/
@[reducible]
def liftsAddTorsor [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    [Nonempty (lifts p f x)] :
    AddTorsor (tangentTensor f hI x0) (lifts p f x) :=
  { liftsAddAction f hf hI x φ with
    vsub := liftsTensorVSub f hf hI x φ
    vsub_vadd' := liftsTensorVSub_vadd f hf hI x φ
    vadd_vsub' := liftsTensorVAdd_vsub f hf hI x φ }

/-- `liftsAddTorsor` subtracts by `liftsTensorVSub`. -/
theorem liftsAddTorsor_vsub [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    [Nonempty (lifts p f x)] (x'' x' : lifts p f x) :
    (liftsAddTorsor f hf hI x φ).vsub x'' x' =
      liftsTensorVSub f hf hI x φ x'' x' := rfl

/-- The tensor action of `θ` sends `x'` to `x''` if and only if the transported
difference recovers `θ`. -/
theorem liftsAddTorsor_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' x'' : lifts p f x) :
    liftsTensorVAdd f hf hI x φ θ x' = x'' ↔
      liftsTensorVSub f hf hI x φ x'' x' = θ := sorry

end CategoryTheory.Functor
