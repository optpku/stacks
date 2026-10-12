/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Definition_90_17_1_ObjectLift
public import stacks_project.Chap90.Lemma_90_16_6
public import stacks_project.Chap90.Remark_90_6_4
public import stacks_project.Chap90.Remark_90_17_3_Tensor
public import stacks_project.Chap90.«90_17_5_1»
public import stacks_project.Chap90.«90_17_5_2_LiftsEquiv»
public import stacks_project.Chap90.«90_17_5_3_Pullback»

/-!
# Free transitive action of `T F_x0 ⊗[k] I` on lifts

For a deformation category and a surjection `f : A' ⟶ A` whose kernel `I` is
annihilated by `m_{A'}`, the composite of the bijections 90.17.5.1–3 yields an
action of `Lift(x0, k[I])` on `Lift(x, A')`. The acting group identifies with
`T F_x0 ⊗[k] I` along `liftsSquareZeroLinearEquiv`.

The comparison of 90.17.5.3 is reconstructed here under a non-clashing name:
`90_17_5_3` and `Remark_90_17_3_Tensor` both export `instIsFiberedInGroupoids_op`,
so they cannot be imported together.
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

/-- Deformation categories satisfy the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_ofIsDeformationCategory [IsDeformationCategory p] :
    HasRimSchlessinger p :=
  IsDeformationCategory.hasRimSchlessinger

/-- Postcompose a lift of `x` to `A' ×_k k[I]` with a residue pushforward `x ⟶ x0`. -/
def ObjectLift.compResiduePushforward
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    {f : A' ⟶ A} {x : p.Fiber A} {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' I f) x) :
    ObjectLift p (squareZeroPullbackSndToResidue A' I) x0 :=
  ⟨Over.mk (a.hom ≫ φ), sorry⟩

/-- `ObjectLift.compResiduePushforward` is postcomposition of the underlying total
morphism with `φ`. -/
theorem ObjectLift.compResiduePushforward_hom
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    {f : A' ⟶ A} {x : p.Fiber A} {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ]
    (a : ObjectLift p (squareZeroPullbackToBase A' I f) x) :
    (ObjectLift.compResiduePushforward φ a).hom = a.hom ≫ φ := sorry

/-- Restriction of a lift along `A' ×_k k[I] ⟶ A` and `A' ×_k k[I] ⟶ k[I]`,
after composing with a residue pushforward `x ⟶ x0`. This reconstructs the
comparison of 90.17.5.3 under a non-clashing name. -/
def liftsSquareZeroComparison [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    lifts p (squareZeroPullbackToBase A' (kerModule f hI) f) x →
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 :=
  let I := kerModule f hI
  Quotient.lift
    (fun a ↦
      (Quotient.mk'' (ObjectLift.pushforwardAlong (squareZeroPullbackFst A' I) f a),
        Quotient.mk''
          (ObjectLift.pushforwardAlong (squareZeroPullbackSnd A' I)
            (squareZeroToResidue Λ k I) (ObjectLift.compResiduePushforward φ a))))
    sorry

/-- The reconstructed comparison of 90.17.5.3 is bijective. -/
theorem liftsSquareZeroComparison_bijective [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    Function.Bijective (liftsSquareZeroComparison f hf hI x φ) := sorry

/-- The bijection of 90.17.5.3, as an equivalence. -/
def liftsSquareZeroPullbackEquiv [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    lifts p (squareZeroPullbackToBase A' (kerModule f hI) f) x ≃
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 :=
  Equiv.ofBijective (liftsSquareZeroComparison f hf hI x φ)
    (liftsSquareZeroComparison_bijective f hf hI x φ)

/-- The underlying function of `liftsSquareZeroPullbackEquiv` is
`liftsSquareZeroComparison`. -/
theorem liftsSquareZeroPullbackEquiv_spec [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    (liftsSquareZeroPullbackEquiv f hf hI x φ).toFun =
      liftsSquareZeroComparison f hf hI x φ := sorry

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
  sorry

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
          (ObjectLift.compResiduePushforward φ a)) := sorry

/-- The composite bijection Φ of 90.17.5.1–3. -/
def liftsPairEquiv [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    lifts p f x × lifts p f x ≃
      lifts p f x × lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 :=
  (liftsSelfPullbackEquiv f hf x).trans
    ((liftsSelfPullbackIsoEquiv f hf hI x).trans
      (liftsSquareZeroPullbackEquiv f hf hI x φ))

/-- Φ commutes with first projections. -/
theorem liftsPairEquiv_fst [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (x1 x2 : lifts p f x) :
    (liftsPairEquiv f hf hI x φ (x1, x2)).1 = x1 := sorry

/-- The inverse of Φ commutes with first projections. -/
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
    liftsVSub f hf hI x φ x'' x' = (liftsPairEquiv f hf hI x φ (x', x'')).2 := sorry

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

/-- The identification `Lift(x0, k[I]) ≃ₗ[k] T F_x0 ⊗[k] I` of Remark 90.17.3. -/
abbrev liftsTangentTensorEquiv [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    lifts p (squareZeroToResidue Λ k (kerModule f hI)) x0 ≃ₗ[k] tangentTensor f hI x0 :=
  liftsSquareZeroLinearEquiv p x0 (FGModuleCat.of k (kerModule f hI))

/-- `liftsTangentTensorEquiv` is `liftsSquareZeroLinearEquiv` at `kerModule f hI`. -/
theorem liftsTangentTensorEquiv_spec [IsDeformationCategory p]
    (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    liftsTangentTensorEquiv f hI x0 =
      liftsSquareZeroLinearEquiv p x0 (FGModuleCat.of k (kerModule f hI)) := sorry

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
      liftsVAdd f hf hI x φ ((liftsTangentTensorEquiv f hI x0).symm θ) x' := sorry

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
      liftsTangentTensorEquiv f hI x0 (liftsVSub f hf hI x φ x'' x') := sorry

/-- The additive action of `T F_x0 ⊗[k] I` on `Lift(x, A')`. -/
@[reducible]
def instAddAction_lifts [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ] :
    AddAction (tangentTensor f hI x0) (lifts p f x) where
  vadd := liftsTensorVAdd f hf hI x φ
  add_vadd := sorry
  zero_vadd := sorry

/-- `instAddAction_lifts` acts by `liftsTensorVAdd`. -/
theorem instAddAction_lifts_vadd [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x) :
    (instAddAction_lifts f hf hI x φ).vadd θ x' =
      liftsTensorVAdd f hf hI x φ θ x' := sorry

/-- If `Lift(x, A')` is nonempty, then `T F_x0 ⊗[k] I` acts freely and transitively
on it. -/
@[reducible]
def instAddTorsor_lifts [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    [Nonempty (lifts p f x)] :
    AddTorsor (tangentTensor f hI x0) (lifts p f x) :=
  { instAddAction_lifts f hf hI x φ with
    vsub := liftsTensorVSub f hf hI x φ
    vsub_vadd' := sorry
    vadd_vsub' := sorry }

/-- `instAddTorsor_lifts` subtracts by `liftsTensorVSub`. -/
theorem instAddTorsor_lifts_vsub [IsDeformationCategory p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (φ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) φ] [p.IsStronglyCocartesian (toResidue A) φ]
    [Nonempty (lifts p f x)] (x'' x' : lifts p f x) :
    (instAddTorsor_lifts f hf hI x φ).vsub x'' x' =
      liftsTensorVSub f hf hI x φ x'' x' := sorry

end CategoryTheory.Functor
