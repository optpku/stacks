module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap94.«94_16_1_1_CanonicalHom»

/-!
# Canonical 1-morphism from a kernel-pair quotient stack

The 1-morphism `f_can : [U/R] ⟶ X` induced by a 1-morphism from a space-representable
algebraic stack, together with full faithfulness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids Functor Opposite TypeCat
open BasedNatIso
open scoped Bicategory CategoricalPullback CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The identity-index isomorphism `Over.mk φ.left ≅ T` for a morphism to `Over.mk (𝟙 S)`. -/
def extendBaseIdOverIso {S : Scheme.{u}} {T : Over S} (φ : T ⟶ Over.mk (𝟙 S)) :
    Over.mk φ.left ≅ T :=
  Over.isoMk (Iso.refl T.left) sorry

/-- Transport a section of `extendBase (𝟙 S) F` to the coproduct formula of `j_!`. -/
def extendBaseIdSection {S : Scheme.{u}} (F : AlgebraicSpace S) {T : (Over S)ᵒᵖ}
    (σ : (extendBase (𝟙 S) F).functorOfPoints.obj T) :
    (extendBasePresheaf (𝟙 S) F.functorOfPoints).obj T :=
  σ

/-- Reconstruct a section of `extendBase (𝟙 S) F` from a coproduct pair. -/
def extendBaseIdSectionInv {S : Scheme.{u}} (F : AlgebraicSpace S) {T : (Over S)ᵒᵖ}
    (σ : (extendBasePresheaf (𝟙 S) F.functorOfPoints).obj T) :
    (extendBase (𝟙 S) F).functorOfPoints.obj T :=
  σ

/-- The identity-index projection of a coproduct section of `j_!`. -/
def extendBaseIdValue {S : Scheme.{u}} (F : AlgebraicSpace S) {T : (Over S)ᵒᵖ}
    (σ : (extendBasePresheaf (𝟙 S) F.functorOfPoints).obj T) :
    F.functorOfPoints.obj T :=
  F.functorOfPoints.map (extendBaseIdOverIso σ.1).inv.op σ.2

/-- The identity change-of-base of an algebraic space over `S` maps to the original space by
projecting the unique index `T ⟶ Over.mk (𝟙 S)`. -/
def extendBaseIdHom {S : Scheme.{u}} (F : AlgebraicSpace S) :
    extendBase (𝟙 S) F ⟶ F where
  app T := ofHom fun σ => extendBaseIdValue F (extendBaseIdSection F σ)
  naturality := fun _ _ _ => sorry

/-- `extendBaseIdHom` evaluates by transporting to the coproduct formula and applying the
identity-index projection. -/
theorem extendBaseIdHom_app {S : Scheme.{u}} (F : AlgebraicSpace S)
    (T : (Over S)ᵒᵖ) (σ : (extendBase (𝟙 S) F).functorOfPoints.obj T) :
    (extendBaseIdHom F).app T σ =
      extendBaseIdValue F (extendBaseIdSection F σ) :=
  sorry

/-- The identity-index inclusion of a point of `F` into `extendBase (𝟙 S) F`. -/
def extendBaseIdValueInv {S : Scheme.{u}} (F : AlgebraicSpace S) {T : (Over S)ᵒᵖ}
    (x : F.functorOfPoints.obj T) :
    (extendBasePresheaf (𝟙 S) F.functorOfPoints).obj T :=
  ⟨Over.homMk T.unop.hom (Category.comp_id T.unop.hom),
    F.functorOfPoints.map
      (extendBaseIdOverIso
        (Over.homMk T.unop.hom (Category.comp_id T.unop.hom))).hom.op x⟩

/-- The inverse identity-index inclusion of an algebraic space into its change-of-base along
`𝟙 S`. -/
def extendBaseIdInv {S : Scheme.{u}} (F : AlgebraicSpace S) :
    F ⟶ extendBase (𝟙 S) F where
  app T := ofHom fun x => extendBaseIdSectionInv F (extendBaseIdValueInv F x)
  naturality := fun _ _ _ => sorry

/-- `extendBaseIdHom` and `extendBaseIdInv` are inverse morphisms of algebraic spaces. -/
def extendBaseIdIso {S : Scheme.{u}} (F : AlgebraicSpace S) :
    extendBase (𝟙 S) F ≅ F where
  hom := extendBaseIdHom F
  inv := extendBaseIdInv F
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)

/-- An algebraic stack is a stack on the big fppf site of `S`. -/
instance instIsStackOnSite (Y : GroupoidsOver S) [AlgebraicStack Y] :
    IsStack.OnSite (Scheme.fppfTopology.over S) Y.p :=
  IsStack.InGroupoids.toOnSite inferInstance

/-- A `T`-valued point of an algebraic space as an object of the standard fiber of its groupoid
fibration. -/
def pointAsPresentedFiber {F : AlgebraicSpace S} {T : Over S}
    (x : F.functorOfPoints.obj (op T)) :
    F.toGroupoids.p.Fiber T :=
  FiberedCategoryOver.Sets.ofPresheaf.valueToFiber F.functorOfPoints T x

/-- `pointAsPresentedFiber` is the tautological category-of-elements fiber object. -/
theorem pointAsPresentedFiber_eq {F : AlgebraicSpace S} {T : Over S}
    (x : F.functorOfPoints.obj (op T)) :
    pointAsPresentedFiber x =
      FiberedCategoryOver.Sets.ofPresheaf.valueToFiber F.functorOfPoints T x :=
  sorry

/-- Transport `f` through the identity change-of-base of the chosen presentation of `U`. -/
def fFromObjectSpace [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    ((groupoid f hU).U.left).toGroupoids ⟶ X :=
  toGroupoids.map (extendBaseIdHom (representingSpace hU)) ≫
    (representingEquiv hU).inv ≫ f

/-- `fFromObjectSpace` is `f` after presenting the object space of the kernel-pair groupoid. -/
theorem fFromObjectSpace_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U) :
    fFromObjectSpace f hU =
      toGroupoids.map (extendBaseIdHom (representingSpace hU)) ≫
        (representingEquiv hU).inv ≫ f :=
  sorry

/-- The image of a `T`-point of the object space under `f`, as a fiber object of `X`. -/
def pointAsXFiber [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).U.left).functorOfPoints.obj (op T)) :
    X.p.Fiber T :=
  (fiberFunctor (fFromObjectSpace f hU) T).obj (pointAsPresentedFiber x)

/-- `pointAsXFiber` is the fiber functor of `fFromObjectSpace` on the presented point. -/
theorem pointAsXFiber_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).U.left).functorOfPoints.obj (op T)) :
    pointAsXFiber f hU x =
      (fiberFunctor (fFromObjectSpace f hU) T).obj (pointAsPresentedFiber x) :=
  sorry

/-- Restrict a co-Grothendieck fiber along the identity-type identification of the point
groupoid. -/
def coGrothendieckPoint [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    (a : (groupoid f hU).preQuotient.total) :
    ((groupoid f hU).U.left).functorOfPoints.obj (op a.base) :=
  a.fiber

/-- `coGrothendieckPoint` is the object-space point underlying a co-Grothendieck object. -/
theorem coGrothendieckPoint_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    (a : (groupoid f hU).preQuotient.total) :
    coGrothendieckPoint f hU a = a.fiber :=
  sorry

/-- A `T`-point of the object space of the kernel-pair groupoid, as an object of `U`. -/
def presentedPointToU [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).U.left).functorOfPoints.obj (op T)) :
    U.p.Fiber T :=
  (fiberFunctor
      (toGroupoids.map (extendBaseIdHom (representingSpace hU)) ≫
        (representingEquiv hU).inv)
      T).obj
    (pointAsPresentedFiber x)

/-- `presentedPointToU` is the fibre functor of the chosen presentation of `U`. -/
theorem presentedPointToU_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).U.left).functorOfPoints.obj (op T)) :
    presentedPointToU f hU x =
      (fiberFunctor
          (toGroupoids.map (extendBaseIdHom (representingSpace hU)) ≫
            (representingEquiv hU).inv)
          T).obj
        (pointAsPresentedFiber x) :=
  sorry

/-- The image of a co-Grothendieck object in the fibre of `X`. -/
def fPreObjFiber [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    (a : (groupoid f hU).preQuotient.total) :
    X.p.Fiber a.base :=
  (fiberFunctor f a.base).obj (presentedPointToU f hU (coGrothendieckPoint f hU a))

/-- `fPreObjFiber` applies `f` to the presented object-space point. -/
theorem fPreObjFiber_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    (a : (groupoid f hU).preQuotient.total) :
    fPreObjFiber f hU a =
      (fiberFunctor f a.base).obj (presentedPointToU f hU (coGrothendieckPoint f hU a)) :=
  sorry

/-- A `T`-point of the arrow space of the kernel-pair groupoid, as an object of the kernel
pair. -/
def presentedPointToKernelPair [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).R.left).functorOfPoints.obj (op T)) :
    (kernelPair f).p.Fiber T :=
  (fiberFunctor
      (toGroupoids.map
          (extendBaseIdHom
            (representingSpace (kernelPair_isRepresentableByAlgebraicSpace f hU))) ≫
        (representingEquiv
          (kernelPair_isRepresentableByAlgebraicSpace f hU)).inv)
      T).obj
    (pointAsPresentedFiber x)

/-- `presentedPointToKernelPair` is the fibre functor of the chosen presentation of the kernel
pair, applied to the tautological fibre object of the arrow space. -/
theorem presentedPointToKernelPair_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {T : Over S} (x : ((groupoid f hU).R.left).functorOfPoints.obj (op T)) :
    presentedPointToKernelPair f hU x =
      (fiberFunctor
          (toGroupoids.map
              (extendBaseIdHom
                (representingSpace (kernelPair_isRepresentableByAlgebraicSpace f hU))) ≫
            (representingEquiv
              (kernelPair_isRepresentableByAlgebraicSpace f hU)).inv)
          T).obj
        (pointAsPresentedFiber x) :=
  sorry

/-- The fibre component of a co-Grothendieck arrow as a morphism of functor-of-points. -/
def coGrothendieckFiberHom [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (groupoid f hU).FunctorPointHom
      (coGrothendieckPoint f hU a)
      ((groupoid f hU).U.left.functorOfPoints.map φ.base.op
        (coGrothendieckPoint f hU b)) :=
  φ.fiber

/-- `coGrothendieckFiberHom` is the fibre component of the co-Grothendieck arrow. -/
theorem coGrothendieckFiberHom_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    coGrothendieckFiberHom f hU φ = φ.fiber :=
  sorry

/-- The kernel-pair fibre object over `a.base` represented by the fibre of `φ`. -/
def fiberAsKernelPair [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (kernelPair f).p.Fiber a.base :=
  presentedPointToKernelPair f hU (coGrothendieckFiberHom f hU φ).arrow

/-- `fiberAsKernelPair` presents the underlying arrow of the co-Grothendieck fibre. -/
theorem fiberAsKernelPair_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fiberAsKernelPair f hU φ =
      presentedPointToKernelPair f hU (coGrothendieckFiberHom f hU φ).arrow :=
  sorry

/-- The switched comparison triple `(b, a, α)` stored by the kernel-pair object associated to
the fibre of `φ`. -/
def switchedComparisonOfFiber [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :=
  BasedCategory.PseudoPullback.fiberObj (fiberAsKernelPair f hU φ).1

/-- `switchedComparisonOfFiber` is the fibrewise categorical pullback object of the kernel-pair
object associated to `φ`. -/
theorem switchedComparisonOfFiber_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    switchedComparisonOfFiber f hU φ =
      BasedCategory.PseudoPullback.fiberObj (fiberAsKernelPair f hU φ).1 :=
  sorry

/-- The fibrewise comparison isomorphism `α : f(pr₀(r)) ≅ f(pr₁(r))` of the kernel-pair object
associated to `φ`. -/
def fiberComparisonIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor f).obj
        (BasedCategory.PseudoPullback.fstObj (fiberAsKernelPair f hU φ).1) ≅
      (toFunctor f).obj
        (BasedCategory.PseudoPullback.sndObj (fiberAsKernelPair f hU φ).1) :=
  BasedCategory.PseudoPullback.comparisonIsoApp (fiberAsKernelPair f hU φ).1

/-- `fiberComparisonIso` is the objectwise comparison of the kernel-pair object of `φ`. -/
theorem fiberComparisonIso_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fiberComparisonIso f hU φ =
      BasedCategory.PseudoPullback.comparisonIsoApp (fiberAsKernelPair f hU φ).1 :=
  sorry

/-- The kernel-pair object of `φ`, viewed in `U` via `pr₁ = s`. -/
def kernelPairSource [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    U.p.Fiber a.base :=
  (fiberFunctor (pr1 f) a.base).obj (fiberAsKernelPair f hU φ)

/-- `kernelPairSource` is the fibre functor of `pr1` on the kernel-pair object of `φ`. -/
theorem kernelPairSource_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairSource f hU φ =
      (fiberFunctor (pr1 f) a.base).obj (fiberAsKernelPair f hU φ) :=
  sorry

/-- The kernel-pair object of `φ`, viewed in `U` via `pr₀ = t`. -/
def kernelPairTarget [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    U.p.Fiber a.base :=
  (fiberFunctor (pr0 f) a.base).obj (fiberAsKernelPair f hU φ)

/-- `kernelPairTarget` is the fibre functor of `pr0` on the kernel-pair object of `φ`. -/
theorem kernelPairTarget_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairTarget f hU φ =
      (fiberFunctor (pr0 f) a.base).obj (fiberAsKernelPair f hU φ) :=
  sorry

/-- The fibrewise comparison `f(t(r)) ≅ f(s(r))` of the kernel-pair object of `φ`. -/
def fPreKernelComparison [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor f a.base).obj (kernelPairTarget f hU φ) ≅
      (fiberFunctor f a.base).obj (kernelPairSource f hU φ) where
  hom := ⟨(fiberComparisonIso f hU φ).hom, sorry⟩
  inv := ⟨(fiberComparisonIso f hU φ).inv, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `fPreKernelComparison` is the fibre packaging of `fiberComparisonIso`. -/
theorem fPreKernelComparison_hom [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (fPreKernelComparison f hU φ).hom.1 = (fiberComparisonIso f hU φ).hom :=
  sorry

/-- The kernel-pair source `pr₁(r)` is the presented object-space point of the co-Grothendieck
source of `φ`. -/
theorem kernelPairSource_eq_presented [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairSource f hU φ =
      presentedPointToU f hU (coGrothendieckPoint f hU a) :=
  sorry

/-- The source object of `φ` as a presented `U`-point, identified with `pr₁(r)` after
transporting the groupoid source equality `s(r) = a`. -/
def fPreSourceUIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairSource f hU φ ≅
      presentedPointToU f hU (coGrothendieckPoint f hU a) :=
  eqToIso (kernelPairSource_eq_presented f hU φ)

/-- The target object of `φ` over `a.base`, obtained by restricting the presented point of `b`. -/
def fPreRestrictedTarget [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    U.p.Fiber a.base :=
  presentedPointToU f hU
    ((groupoid f hU).U.left.functorOfPoints.map φ.base.op
      (coGrothendieckPoint f hU b))

/-- `fPreRestrictedTarget` is the presented restriction of the target point of `φ`. -/
theorem fPreRestrictedTarget_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreRestrictedTarget f hU φ =
      presentedPointToU f hU
        ((groupoid f hU).U.left.functorOfPoints.map φ.base.op
          (coGrothendieckPoint f hU b)) :=
  sorry

/-- The kernel-pair target `pr₀(r)` is the restricted presented target of `φ`. -/
theorem kernelPairTarget_eq_restricted [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairTarget f hU φ = fPreRestrictedTarget f hU φ :=
  sorry

/-- The kernel-pair target `pr₀(r)` identifies with the restricted presented target of `φ`
after transporting the groupoid target equality `t(r) = b|_{φ.base}`. -/
def fPreTargetRestrictIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairTarget f hU φ ≅ fPreRestrictedTarget f hU φ :=
  eqToIso (kernelPairTarget_eq_restricted f hU φ)

/-- Restriction of a presented `U`-point along `φ.base` is selected reindexing in `U`. -/
theorem fPreRestrictedTarget_eq_reindex [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreRestrictedTarget f hU φ =
      Chosen.reindexObj U.p φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b)) :=
  sorry

/-- Selected-cleavage comparison identifying restriction of a presented `U`-point with
reindexing in `U`. -/
def fPreTargetReindexIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreRestrictedTarget f hU φ ≅
      Chosen.reindexObj U.p φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b)) :=
  eqToIso (fPreRestrictedTarget_eq_reindex f hU φ)

/-- Composite identification of `pr₀(r)` with the selected reindexing of the presented target. -/
def fPreTargetUIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    kernelPairTarget f hU φ ≅
      Chosen.reindexObj U.p φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b)) :=
  fPreTargetRestrictIso f hU φ ≪≫ fPreTargetReindexIso f hU φ

/-- The switched comparison isomorphism `α : f(φ.base⁎ b) ≅ f(a)` obtained by transporting the
kernel-pair comparison of `φ.fiber` to the presented objects of `U`. -/
def fPreAlpha [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor f a.base).obj
        (Chosen.reindexObj U.p φ.base
          (presentedPointToU f hU (coGrothendieckPoint f hU b))) ≅
      (fiberFunctor f a.base).obj
        (presentedPointToU f hU (coGrothendieckPoint f hU a)) :=
  ((fiberFunctor f a.base).mapIso (fPreTargetUIso f hU φ)).symm ≪≫
    fPreKernelComparison f hU φ ≪≫
    (fiberFunctor f a.base).mapIso (fPreSourceUIso f hU φ)

/-- The switched comparison triple `(b, a, α)` on presented objects of `U`. -/
def fPreSwitched [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor f a.base) ⊡ (fiberFunctor f a.base) :=
  ofSwitchedComparison f
    (presentedPointToU f hU (coGrothendieckPoint f hU a))
    (Chosen.reindexObj U.p φ.base
      (presentedPointToU f hU (coGrothendieckPoint f hU b)))
    (fPreAlpha f hU φ)

/-- `fPreSwitched` is `ofSwitchedComparison` of the presented source, reindexed target, and
transported kernel-pair comparison. -/
theorem fPreSwitched_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreSwitched f hU φ =
      ofSwitchedComparison f
        (presentedPointToU f hU (coGrothendieckPoint f hU a))
        (Chosen.reindexObj U.p φ.base
          (presentedPointToU f hU (coGrothendieckPoint f hU b)))
        (fPreAlpha f hU φ) :=
  sorry

/-- Selected-cleavage comparison `φ.base⁎ (f(b)) ≅ f(φ.base⁎ b)` for `f`. -/
def fPreReindexIso [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    Chosen.reindexObj X.p φ.base (fPreObjFiber f hU b) ≅
      (fiberFunctor f a.base).obj
        (Chosen.reindexObj U.p φ.base
          (presentedPointToU f hU (coGrothendieckPoint f hU b))) :=
  CartesianBasedFunctor.Reindex.mapIso
    (toCartesianBasedFunctor f)
    (Cleavage.ofIsFibered U.p)
    (Cleavage.ofIsFibered X.p) φ.base
    (presentedPointToU f hU (coGrothendieckPoint f hU b))

/-- `fPreReindexIso` is the selected-cleavage reindexing comparison of `f`. -/
theorem fPreReindexIso_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreReindexIso f hU φ =
      CartesianBasedFunctor.Reindex.mapIso
        (toCartesianBasedFunctor f)
        (Cleavage.ofIsFibered U.p)
        (Cleavage.ofIsFibered X.p) φ.base
        (presentedPointToU f hU (coGrothendieckPoint f hU b)) :=
  sorry

/-- The vertical image of a co-Grothendieck fibre: `canonicalHom` of the switched comparison
`(b, a, α)`, i.e. `α.inv : f(a) ⟶ f(b)`, as a total morphism of `X`. -/
def fPreVertical [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (fPreObjFiber f hU a).1 ⟶
      (Chosen.reindexObj X.p φ.base (fPreObjFiber f hU b)).1 :=
  (canonicalHom f (fPreSwitched f hU φ)).1 ≫ (fPreReindexIso f hU φ).inv.1

/-- `fPreVertical` is `canonicalHom` of the switched presented comparison, composed with the
reindexing comparison of `f`. -/
theorem fPreVertical_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreVertical f hU φ =
      (canonicalHom f (fPreSwitched f hU φ)).1 ≫ (fPreReindexIso f hU φ).inv.1 :=
  sorry

/-- `canonicalHom` of the switched comparison of `φ.fiber` is the inverse of `fPreAlpha`. -/
theorem fPreSwitched_canonicalHom [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    canonicalHom f (fPreSwitched f hU φ) = (fPreAlpha f hU φ).inv :=
  sorry

/-- The total-category functor of the prestack map `[U /ₚ R] ⟶ X` induced by `f`. On objects it
sends a `T`-point of `U` to `f` of the corresponding object. On a co-Grothendieck arrow `φ` it
sends the fibre component to `canonicalHom` of the switched comparison `(b, a, α)` and then
composes with the selected cartesian lift of `φ.base`. -/
def fPreTotal [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (groupoid f hU).preQuotient.total ⥤ X.total where
  obj a := (fPreObjFiber f hU a).1
  map {a b} φ :=
    fPreVertical f hU φ ≫
      Chosen.cartesianHom X.p φ.base (fPreObjFiber f hU b)
  map_id := sorry
  map_comp := sorry

/-- On morphisms, `fPreTotal` composes the vertical `canonicalHom` image of `φ.fiber` with the
selected cartesian lift of `φ.base`. -/
theorem fPreTotal_map_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    (fPreTotal f hU).map φ =
      (canonicalHom f (fPreSwitched f hU φ)).1 ≫
        (fPreReindexIso f hU φ).inv.1 ≫
        Chosen.cartesianHom X.p φ.base (fPreObjFiber f hU b) :=
  sorry

/-- The fibrewise image of a co-Grothendieck arrow recovers `canonicalHom` of the switched
comparison `(b, a, α)`, i.e. `α.inv : f(a) ⟶ f(b)`. -/
theorem fPreTotal_map_canonicalHom [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    {a b : (groupoid f hU).preQuotient.total} (φ : a ⟶ b) :
    fPreVertical f hU φ =
      (canonicalHom f (fPreSwitched f hU φ)).1 ≫ (fPreReindexIso f hU φ).inv.1 :=
  sorry

/-- The prestack map `[U /ₚ R] ⟶ X` commutes strictly with the projections to `Over S`. -/
theorem fPreTotal_w [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    fPreTotal f hU ⋙ X.p = (groupoid f hU).preQuotient.p :=
  sorry

/-- The 1-morphism `[U /ₚ R] ⟶ X` induced by `f`. -/
def fPre [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (groupoid f hU).preQuotient ⟶ X :=
  ofBasedFunctor
    { toFunctor := fPreTotal f hU
      w := fPreTotal_w f hU }

/-- `fPre` is the groupoid-fibred morphism associated to `fPreTotal`. -/
theorem fPre_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    toFunctor (fPre f hU) = fPreTotal f hU :=
  sorry

/-- The cartesian based functor underlying `fPre`. -/
def fPreCartesian [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    CartesianBasedFunctor ((groupoid f hU).preQuotient.p) X.p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (fPreTotal f hU) (fPreTotal_w f hU))

/-- `fPreCartesian` is the cartesian based functor associated to `fPreTotal`. -/
theorem fPreCartesian_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (fPreCartesian f hU).toBasedFunctor =
      BasedFunctor.ofFunctor (fPreTotal f hU) (fPreTotal_w f hU) :=
  sorry

/-- The selected stackification lift of `fPre` through `[U /ₚ R] ⟶ [U / R]`. -/
def fCanLift [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (groupoid f hU).stackificationPresentation.comparison)
      (fPreCartesian f hU) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (groupoid f hU).stackificationPresentation.isStackification
    (fPreCartesian f hU)

/-- The canonical 1-morphism `f_can : [U/R] ⟶ X` of stacks in groupoids over
`(Sch/S)_fppf` induced by `f`. -/
def fCan [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (groupoid f hU).quotientStack ⟶ X :=
  ofBasedFunctor (CartesianBasedFunctor.toBasedFunctor (fCanLift f hU).lift)

/-- `fCan` is the groupoid-fibred morphism associated to the selected stackification lift of
`fPre`. -/
theorem fCan_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    toBasedFunctor (fCan f hU) =
      CartesianBasedFunctor.toBasedFunctor (fCanLift f hU).lift :=
  sorry

/-- The stackification comparison identifying the precomposition of `fCan` with `fPre`. -/
def fCanLift_comparison [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (CartesianBasedFunctor.precomp X.p
        (groupoid f hU).stackificationPresentation.comparison).obj
      (fCanLift f hU).lift ≅ fPreCartesian f hU :=
  (fCanLift f hU).comparison

/-- `fCanLift_comparison` is the comparison field of the selected stackification lift. -/
theorem fCanLift_comparison_eq [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U) :
    fCanLift_comparison f hU = (fCanLift f hU).comparison :=
  sorry

/-- The atlas composite of `fCan`. -/
def fCan_atlas [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    (groupoid f hU).U.left.toGroupoids ⟶ X :=
  (groupoid f hU).atlas ≫ fCan f hU

/-- `fCan_atlas` is the composite of the quotient atlas with `fCan`. -/
theorem fCan_atlas_eq [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    fCan_atlas f hU = (groupoid f hU).atlas ≫ fCan f hU :=
  sorry

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
