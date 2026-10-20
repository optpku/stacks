module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.SquareZero

/-!
# Comparison of lifts along a square-zero fibre product
-/

@[expose] public section

open CategoryTheory IsLocalRing
open CategoryTheory.Functor CategoryTheory.Functor.Fiber ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsDeformationCategory p]
variable {A' A : ArtinianLocalAlgCat Λ k}

/- 90.17.5.3: a chosen residue pushforward induces the comparison
from lifts of `x` to `A' ×_k k[I]` to pairs of lifts of `x` to `A'` and of `x0` to `k[I]`,
where `I` is the kernel annihilated by the maximal ideal. -/
@[stacks 06TC] #check (CategoryTheory.Functor.liftsSquareZeroPullback :
  ∀ (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ],
    lifts p (squareZeroPullbackToBase A' (kerModule f h_ann) f) x →
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f h_ann)) x0)

variable (f : A' ⟶ A) (hf : Function.Surjective f.hom)
  (h_ann : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
  (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
  (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
  [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]

#check (CategoryTheory.Functor.liftsSquareZeroPullback_bijective f hf h_ann x φ :
  Function.Bijective (CategoryTheory.Functor.liftsSquareZeroPullback f hf h_ann x φ))

#check (CategoryTheory.Functor.liftsSquareZeroPullback_fst f hf h_ann x φ :
  ∀ (a : ObjectLift p (squareZeroPullbackToBase A' (kerModule f h_ann) f) x),
    (CategoryTheory.Functor.liftsSquareZeroPullback f hf h_ann x φ (Quotient.mk'' a)).1 =
      Quotient.mk'' (ObjectLift.pushforwardAlong (squareZeroPullbackFst A' (kerModule f h_ann))
        f a))

#check (CategoryTheory.Functor.liftsSquareZeroPullback_snd f hf h_ann x φ :
  ∀ (a : ObjectLift p (squareZeroPullbackToBase A' (kerModule f h_ann) f) x),
    (CategoryTheory.Functor.liftsSquareZeroPullback f hf h_ann x φ (Quotient.mk'' a)).2 =
      Quotient.mk'' (ObjectLift.pushforwardAlong (squareZeroPullbackSnd A' (kerModule f h_ann))
        (squareZeroToResidue Λ k (kerModule f h_ann)) (ObjectLift.compSquareZeroResidue φ a)))
