/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Kernel
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.CategoryTheory.Fibered.Lifts.Pushforward

/-!
# Comparison of lifts over a square-zero pullback
-/

@[expose] public section

open CategoryTheory IsLocalRing
open Functor Fiber ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

variable {A' A : ArtinianLocalAlgCat Λ k}

/-- Postcompose a lift of `x` to `A' ×_k k[I]` with a residue pushforward `x ⟶ x0`, obtaining
a lift of `x0` along `A' ×_k k[I] ⟶ k[I] ⟶ k`. -/
noncomputable def ObjectLift.compSquareZeroResidue
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    {f : A' ⟶ A} {x : p.Fiber A} {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' I f) x) :
    ObjectLift p (squareZeroPullbackSndToResidue A' I) x0 :=
  ⟨Over.mk (a.hom ≫ φ), sorry⟩

/-- A residue pushforward induces a comparison from lifts over the square-zero pullback
to pairs of lifts over the extension and its kernel's square-zero algebra. -/
noncomputable def liftsSquareZeroPullback [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    lifts p (squareZeroPullbackToBase A' (kerModule f h_ann) f) x →
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f h_ann)) x0 :=
  let I := kerModule f h_ann
  Quotient.lift
    (fun a ↦
      (Quotient.mk'' (ObjectLift.pushforwardAlong (squareZeroPullbackFst A' I) f a),
        Quotient.mk'' (ObjectLift.pushforwardAlong (squareZeroPullbackSnd A' I)
          (squareZeroToResidue Λ k I) (ObjectLift.compSquareZeroResidue φ a))))
    sorry

/-- The square-zero pullback comparison of lift classes is a bijection. -/
theorem liftsSquareZeroPullback_bijective [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    Function.Bijective (liftsSquareZeroPullback f hf h_ann x φ) := sorry

/-- The first component of `liftsSquareZeroPullback` is pushforward along the first
projection of `A' ×_k k[I]`. -/
theorem liftsSquareZeroPullback_fst [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' (kerModule f h_ann) f) x) :
    (liftsSquareZeroPullback f hf h_ann x φ (Quotient.mk'' a)).1 =
      Quotient.mk'' (ObjectLift.pushforwardAlong (squareZeroPullbackFst A' (kerModule f h_ann))
        f a) := sorry

/-- The second component of `liftsSquareZeroPullback` is pushforward along the second
projection of `A' ×_k k[I]`, after composing with the chosen residue pushforward. -/
theorem liftsSquareZeroPullback_snd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' (kerModule f h_ann) f) x) :
    (liftsSquareZeroPullback f hf h_ann x φ (Quotient.mk'' a)).2 =
      Quotient.mk'' (ObjectLift.pushforwardAlong
        (squareZeroPullbackSnd A' (kerModule f h_ann)) (squareZeroToResidue Λ k (kerModule f h_ann))
        (ObjectLift.compSquareZeroResidue φ a)) := sorry

end CategoryTheory.Functor
