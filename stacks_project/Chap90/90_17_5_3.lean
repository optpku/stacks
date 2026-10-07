module

public import stacks_project.Chap90.«90_17_5_2_LiftsEquiv»
public import stacks_project.Chap90.«90_17_5_3_Pullback»
public import stacks_project.Chap90.«90_17_5_3_SquareZero»
public import stacks_project.Chap90.Definition_90_16_8

/-!
# Comparison of lifts along a square-zero fibre product

After choosing a pushforward of `x` along `A ⟶ k`, restriction of lifts along the composed
fibre squares `A' ×_k k[I] ⟶ A ×_k k[I] ⟶ k[I]` over `A' ⟶ A ⟶ k` yields a comparison
from lifts of `x` to `A' ×_k k[I]` to the product of lifts of `x` to `A'` and lifts of
`x0` to `k[I]`.
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

/-- Deformation categories are cofibered in groupoids, so `p.op` is fibered in groupoids. -/
instance instIsFiberedInGroupoids_op [IsDeformationCategory p] :
    IsFibered.InGroupoids p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Push a lift of `x` along `u ≫ f` forward along `u`, obtaining a lift along `f`. -/
noncomputable def ObjectLift.pushforwardAlongOf [IsFibered.InGroupoids p.op]
    {P B C : ArtinianLocalAlgCat Λ k} (u : P ⟶ B) (f : B ⟶ C) {x : p.Fiber C}
    (a : ObjectLift p (u ≫ f) x) : ObjectLift p f x :=
  ObjectLift.pushforwardAlong u f a

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

/-- 90.17.5.3: after choosing a pushforward `x ⟶ x0` of `x` along `A ⟶ k`, restriction of
lifts along the composed fibre squares `A' ×_k k[I] ⟶ A ×_k k[I] ⟶ k[I]` over
`A' ⟶ A ⟶ k` yields a comparison
`lifts p (squareZeroPullbackToBase A' I f) x ⟶
  lifts p f x × lifts p (squareZeroToResidue Λ k I) x0`,
where `I = kerModule f h_ann` is annihilated by `m_{A'}`. -/
@[stacks 06TC]
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
      (Quotient.mk'' (ObjectLift.pushforwardAlongOf (squareZeroPullbackFst A' I) f a),
        Quotient.mk''
          (ObjectLift.pushforwardAlongOf (squareZeroPullbackSnd A' I)
            (squareZeroToResidue Λ k I) (ObjectLift.compSquareZeroResidue φ a))))
    sorry

/-- The displayed comparison of lift classes is a bijection. -/
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
      Quotient.mk''
        (ObjectLift.pushforwardAlongOf (squareZeroPullbackFst A' (kerModule f h_ann)) f a) :=
  sorry

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
      Quotient.mk''
        (ObjectLift.pushforwardAlongOf (squareZeroPullbackSnd A' (kerModule f h_ann))
          (squareZeroToResidue Λ k (kerModule f h_ann))
          (ObjectLift.compSquareZeroResidue φ a)) := sorry

end CategoryTheory.Functor
