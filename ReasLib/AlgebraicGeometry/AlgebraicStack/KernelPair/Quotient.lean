/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Groupoid
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalHom

/-! # Morphisms from kernel-pair quotient stacks -/

@[expose] public section
-- The public functor retains its private fibrewise transport formulas.
set_option backward.privateInPublic true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids Functor Opposite TypeCat BasedNatIso
open scoped Bicategory CategoricalPullback CategoryTheory.TwoFibreProduct
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)

/-- Transport `f` through the identity change-of-base of the chosen presentation of `U`. -/
def fFromObjectSpace [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    ((groupoid f hU).U.left).toGroupoids ⟶ X :=
  toGroupoids.map (extendBaseIdHom (IsRepresentableByAlgebraicSpace.representingSpace hU)) ≫
    (IsRepresentableByAlgebraicSpace.representingEquiv hU).inv ≫ f

/-- The image of a `T`-point of the object space under `f`, as a fiber object of `X`. -/
def pointAsXFiber [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).U.left).functorOfPoints.obj (op T)) :
    X.p.Fiber T :=
  (fiberFunctor (fFromObjectSpace f hU) T).obj (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber _ _ x)

/-- Restrict a co-Grothendieck fiber along the identity-type identification of the point
groupoid. -/
def coGrothendieckPoint [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    (a : (SmallQuotient.preQuotient (groupoid f hU)).total) :
    ((groupoid f hU).U.left).functorOfPoints.obj (op a.base) :=
  a.fiber

/-- A `T`-point of the object space of the kernel-pair groupoid, as an object of `U`. -/
def presentedPointToU [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).U.left).functorOfPoints.obj (op T)) :
    U.p.Fiber T :=
  (fiberFunctor
      (toGroupoids.map (extendBaseIdHom (IsRepresentableByAlgebraicSpace.representingSpace hU)) ≫
        (IsRepresentableByAlgebraicSpace.representingEquiv hU).inv)
      T).obj
    (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber _ _ x)

/-- The image of a co-Grothendieck object in the fibre of `X`. -/
def fPreObjFiber [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    (a : (SmallQuotient.preQuotient (groupoid f hU)).total) :
    X.p.Fiber a.base :=
  (fiberFunctor f a.base).obj (presentedPointToU f hU (coGrothendieckPoint f hU a))

/-- A `T`-point of the arrow space of the kernel-pair groupoid, as an object of the kernel
pair. -/
def presentedPointToKernelPair [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).R.left).functorOfPoints.obj (op T)) :
    (KernelPair.kernelPair.{u + 1, u, u + 1} f).p.Fiber T :=
  (fiberFunctor
      (toGroupoids.map
          (extendBaseIdHom
            (IsRepresentableByAlgebraicSpace.representingSpace (kernelPair_isRepresentableByAlgebraicSpace f hU))) ≫
        (IsRepresentableByAlgebraicSpace.representingEquiv
          (kernelPair_isRepresentableByAlgebraicSpace f hU)).inv)
      T).obj
    (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber _ _ x)

/-- The fibre component of a co-Grothendieck arrow as a morphism of functor-of-points. -/
private def coGrothendieckFiberHom [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (groupoid f hU).FunctorPointHom
      (coGrothendieckPoint f hU a)
      ((groupoid f hU).U.left.functorOfPoints.map φ.base.op
        (coGrothendieckPoint f hU b)) :=
  φ.fiber

/-- The kernel-pair fibre object over `a.base` represented by the fibre of `φ`. -/
private def fiberAsKernelPair [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (KernelPair.kernelPair.{u + 1, u, u + 1} f).p.Fiber a.base :=
  presentedPointToKernelPair f hU (coGrothendieckFiberHom f hU φ).arrow

/-- The fibrewise comparison isomorphism `α : f(pr₀(r)) ≅ f(pr₁(r))` of the kernel-pair object
associated to `φ`. -/
private def fiberComparisonIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (toFunctor f).obj
        (BasedCategory.PseudoPullback.fstObj (fiberAsKernelPair f hU φ).1) ≅
      (toFunctor f).obj
        (BasedCategory.PseudoPullback.sndObj (fiberAsKernelPair f hU φ).1) :=
  BasedCategory.PseudoPullback.comparisonIsoApp (fiberAsKernelPair f hU φ).1

/-- The kernel-pair object of `φ`, viewed in `U` via `pr₁ = s`. -/
private def kernelPairSource [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    U.p.Fiber a.base :=
  (fiberFunctor (KernelPair.pr1.{u + 1, u, u + 1} f) a.base).obj (fiberAsKernelPair f hU φ)

/-- The kernel-pair object of `φ`, viewed in `U` via `pr₀ = t`. -/
private def kernelPairTarget [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    U.p.Fiber a.base :=
  (fiberFunctor (KernelPair.pr0.{u + 1, u, u + 1} f) a.base).obj (fiberAsKernelPair f hU φ)

/-- The fibrewise comparison `f(t(r)) ≅ f(s(r))` of the kernel-pair object of `φ`. -/
private def fPreKernelComparison [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (fiberFunctor f a.base).obj (kernelPairTarget f hU φ) ≅
      (fiberFunctor f a.base).obj (kernelPairSource f hU φ) where
  hom := ⟨(fiberComparisonIso f hU φ).hom, sorry⟩
  inv := ⟨(fiberComparisonIso f hU φ).inv, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The kernel-pair source and the presented source of a prestack arrow have equal
values in the representing presheaf. -/
theorem fPreSource_value [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    PresheafKernelPair.value (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints a.base
      ((fiberFunctor (IsRepresentableByAlgebraicSpace.representingEquiv hU).hom a.base).obj
        (kernelPairSource f hU φ)) =
      PresheafKernelPair.value (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints a.base
      ((fiberFunctor (IsRepresentableByAlgebraicSpace.representingEquiv hU).hom a.base).obj
        (presentedPointToU f hU (coGrothendieckPoint f hU a))) := sorry

/-- The source object of `φ` as a presented `U`-point, identified with `pr₁(r)` after
transporting the groupoid source equality `s(r) = a`. -/
def fPreSourceUIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    kernelPairSource f hU φ ≅
      presentedPointToU f hU (coGrothendieckPoint f hU a)  :=
  let e := IsRepresentableByAlgebraicSpace.representingEquiv hU
  let P := (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints
  let x := kernelPairSource f hU φ
  let y := presentedPointToU f hU (coGrothendieckPoint f hU a)
  let unit := BasedNatIso.fiber (toBasedFunctorIso e.unit) a.base
  unit.app x ≪≫ (fiberFunctor e.inv a.base).mapIso
    ((PresheafKernelPair.pointValueIso P a.base ((fiberFunctor e.hom a.base).obj x)).symm ≪≫
      eqToIso (congrArg (PresheafKernelPair.point P a.base) (fPreSource_value f hU φ)) ≪≫
      PresheafKernelPair.pointValueIso P a.base ((fiberFunctor e.hom a.base).obj y)) ≪≫
    (unit.app y).symm

/-- The target object of `φ` over `a.base`, obtained by restricting the presented point of `b`. -/
private def fPreRestrictedTarget [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    U.p.Fiber a.base :=
  presentedPointToU f hU
    ((groupoid f hU).U.left.functorOfPoints.map φ.base.op
      (coGrothendieckPoint f hU b))

/-- The kernel-pair target and the restricted presented target have equal values in the
representing presheaf. -/
theorem fPreTarget_value [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    PresheafKernelPair.value (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints a.base
      ((fiberFunctor (IsRepresentableByAlgebraicSpace.representingEquiv hU).hom a.base).obj
        (kernelPairTarget f hU φ)) =
      PresheafKernelPair.value (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints a.base
      ((fiberFunctor (IsRepresentableByAlgebraicSpace.representingEquiv hU).hom a.base).obj
        (fPreRestrictedTarget f hU φ)) := sorry

/-- The kernel-pair target `pr₀(r)` identifies with the restricted presented target of `φ`
after transporting the groupoid target equality `t(r) = b|_{φ.base}`. -/
private def fPreTargetRestrictIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    kernelPairTarget f hU φ ≅ fPreRestrictedTarget f hU φ  :=
  let e := IsRepresentableByAlgebraicSpace.representingEquiv hU
  let P := (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints
  let x := kernelPairTarget f hU φ
  let y := fPreRestrictedTarget f hU φ
  let unit := BasedNatIso.fiber (toBasedFunctorIso e.unit) a.base
  unit.app x ≪≫ (fiberFunctor e.inv a.base).mapIso
    ((PresheafKernelPair.pointValueIso P a.base ((fiberFunctor e.hom a.base).obj x)).symm ≪≫
      eqToIso (congrArg (PresheafKernelPair.point P a.base) (fPreTarget_value f hU φ)) ≪≫
      PresheafKernelPair.pointValueIso P a.base ((fiberFunctor e.hom a.base).obj y)) ≪≫
    (unit.app y).symm

/-- Restriction and selected reindexing of a presented point have equal values in the
representing presheaf. -/
theorem fPreReindex_value [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    PresheafKernelPair.value (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints a.base
      ((fiberFunctor (IsRepresentableByAlgebraicSpace.representingEquiv hU).hom a.base).obj
        (fPreRestrictedTarget f hU φ)) =
      PresheafKernelPair.value (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints a.base
      ((fiberFunctor (IsRepresentableByAlgebraicSpace.representingEquiv hU).hom a.base).obj
        (Chosen.reindexObj U.p φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b)))) := sorry

/-- Selected-cleavage comparison identifying restriction of a presented `U`-point with
reindexing in `U`. -/
private def fPreTargetReindexIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    fPreRestrictedTarget f hU φ ≅
      Chosen.reindexObj U.p φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b))  :=
  let e := IsRepresentableByAlgebraicSpace.representingEquiv hU
  let P := (IsRepresentableByAlgebraicSpace.representingSpace hU).functorOfPoints
  let x := fPreRestrictedTarget f hU φ
  let y := Chosen.reindexObj U.p φ.base
      (presentedPointToU f hU (coGrothendieckPoint f hU b))
  let unit := BasedNatIso.fiber (toBasedFunctorIso e.unit) a.base
  unit.app x ≪≫ (fiberFunctor e.inv a.base).mapIso
    ((PresheafKernelPair.pointValueIso P a.base ((fiberFunctor e.hom a.base).obj x)).symm ≪≫
      eqToIso (congrArg (PresheafKernelPair.point P a.base) (fPreReindex_value f hU φ)) ≪≫
      PresheafKernelPair.pointValueIso P a.base ((fiberFunctor e.hom a.base).obj y)) ≪≫
    (unit.app y).symm

/-- Composite identification of `pr₀(r)` with the selected reindexing of the presented target. -/
private def fPreTargetUIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    kernelPairTarget f hU φ ≅
      Chosen.reindexObj U.p φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b)) :=
  fPreTargetRestrictIso f hU φ ≪≫ fPreTargetReindexIso f hU φ

/-- The switched comparison isomorphism `α : f(φ.base⁎ b) ≅ f(a)` obtained by transporting the
kernel-pair comparison of `φ.fiber` to the presented objects of `U`. -/
private def fPreAlpha [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (fiberFunctor f a.base).obj
        (Chosen.reindexObj U.p φ.base
          (presentedPointToU f hU (coGrothendieckPoint f hU b))) ≅
      (fiberFunctor f a.base).obj
        (presentedPointToU f hU (coGrothendieckPoint f hU a)) :=
  ((fiberFunctor f a.base).mapIso (fPreTargetUIso f hU φ)).symm ≪≫
    fPreKernelComparison f hU φ ≪≫
    (fiberFunctor f a.base).mapIso (fPreSourceUIso f hU φ)

/-- The switched comparison triple `(b, a, α)` on presented objects of `U`. -/
private def fPreSwitched [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (fiberFunctor f a.base) ⊡ (fiberFunctor f a.base) :=
  ofSwitchedComparison f
    (presentedPointToU f hU (coGrothendieckPoint f hU a))
    (Chosen.reindexObj U.p φ.base
      (presentedPointToU f hU (coGrothendieckPoint f hU b)))
    (fPreAlpha f hU φ)

/-- Selected-cleavage comparison `φ.base⁎ (f(b)) ≅ f(φ.base⁎ b)` for `f`. -/
private def fPreReindexIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    Chosen.reindexObj X.p φ.base (fPreObjFiber f hU b) ≅
      (fiberFunctor f a.base).obj
        (Chosen.reindexObj U.p φ.base
          (presentedPointToU f hU (coGrothendieckPoint f hU b))) :=
  CartesianBasedFunctor.Reindex.mapIso
    (toCartesianBasedFunctor f)
    (Cleavage.ofIsFibered U.p)
    (Cleavage.ofIsFibered X.p) φ.base
    (presentedPointToU f hU (coGrothendieckPoint f hU b))

/-- The vertical image of a co-Grothendieck fibre: `canonicalHom` of the switched comparison
`(b, a, α)`, i.e. `α.inv : f(a) ⟶ f(b)`, as a total morphism of `X`. -/
def fPreVertical [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (fPreObjFiber f hU a).1 ⟶
      (Chosen.reindexObj X.p φ.base (fPreObjFiber f hU b)).1 :=
  (canonicalHom f (fPreSwitched f hU φ)).1 ≫ (fPreReindexIso f hU φ).inv.1

/-- The total-category functor of the prestack map `[U /ₚ R] ⟶ X` induced by `f`. On objects it
sends a `T`-point of `U` to `f` of the corresponding object. On a co-Grothendieck arrow `φ` it
sends the fibre component to `canonicalHom` of the switched comparison `(b, a, α)` and then
composes with the selected cartesian lift of `φ.base`. -/
def fPreTotal [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (SmallQuotient.preQuotient (groupoid f hU)).total ⥤ X.total where
  obj a := (fPreObjFiber f hU a).1
  map {a b} φ :=
    fPreVertical f hU φ ≫
      Chosen.cartesianHom X.p φ.base (fPreObjFiber f hU b)
  map_id := sorry
  map_comp := sorry

/-- On morphisms, the induced prestack functor composes the inverse switched comparison
with the chosen cartesian lift of the base morphism. -/
theorem fPreTotal_map_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (SmallQuotient.preQuotient (groupoid f hU)).total} (φ : a ⟶ b) :
    (fPreTotal f hU).map φ =
      (canonicalHom f (fPreSwitched f hU φ)).1 ≫
        (fPreReindexIso f hU φ).inv.1 ≫
        Chosen.cartesianHom X.p φ.base (fPreObjFiber f hU b) := sorry

/-- The prestack map `[U /ₚ R] ⟶ X` commutes strictly with the projections to `Over S`. -/
theorem fPreTotal_w [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    fPreTotal f hU ⋙ X.p = (SmallQuotient.preQuotient (groupoid f hU)).p :=
  sorry

/-- The 1-morphism `[U /ₚ R] ⟶ X` induced by `f`. -/
def fPre [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (SmallQuotient.preQuotient (groupoid f hU)) ⟶ X :=
  ofBasedFunctor
    { toFunctor := fPreTotal f hU
      w := fPreTotal_w f hU }

/-- The cartesian based functor underlying `fPre`. -/
def fPreCartesian [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    CartesianBasedFunctor ((SmallQuotient.preQuotient (groupoid f hU)).p) X.p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (fPreTotal f hU) (fPreTotal_w f hU))

/-- The selected stackification lift of `fPre` through `[U /ₚ R] ⟶ [U / R]`. -/
def fCanLift [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (SmallQuotient.stackificationPresentation (groupoid f hU)).comparison)
      (fPreCartesian f hU) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (SmallQuotient.stackificationPresentation (groupoid f hU)).isStackification
    (fPreCartesian f hU)

/-- The canonical 1-morphism `f_can : [U/R] ⟶ X` of stacks in groupoids over
`(Sch/S)_fppf` induced by `f`. -/
def fCan [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (SmallQuotient.quotientStack (groupoid f hU)) ⟶ X :=
  ofBasedFunctor (CartesianBasedFunctor.toBasedFunctor (fCanLift f hU).lift)

/-- The stackification comparison identifying the precomposition of `fCan` with `fPre`. -/
def fCanLift_comparison [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (CartesianBasedFunctor.precomp X.p
        (SmallQuotient.stackificationPresentation (groupoid f hU)).comparison).obj
      (fCanLift f hU).lift ≅ fPreCartesian f hU :=
  (fCanLift f hU).comparison

/-- The atlas composite of `fCan`. -/
def fCan_atlas [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (groupoid f hU).U.left.toGroupoids ⟶ X :=
  (SmallQuotient.atlas (groupoid f hU)) ≫ fCan f hU

/-- After presenting `U`, the atlas triangle identifies `f` with `atlas ≫ fCan`. -/
theorem fCan_atlas_iso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    Nonempty (fCan_atlas f hU ≅ fFromObjectSpace f hU) :=
  sorry

/-- The canonical 1-morphism `f_can : [U/R] ⟶ X` is fully faithful. -/
theorem fCan_fullyFaithful [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U) :
    Nonempty (toBasedFunctor (fCan f hU)).FullyFaithful :=
  sorry

end AlgebraicGeometry.AlgebraicStack
