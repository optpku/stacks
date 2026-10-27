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
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Trivial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalHom
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.AutomorphismGroup

/-!
# Canonical 1-morphism from a trivial-action quotient stack

A section `x : U ⟶ X` of a morphism of algebraic stacks determines a canonical
1-morphism `xCan` from the quotient stack `[U/G]` of the trivial action of
`G = Isom_X(x, x)` to `X`.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
open AlgebraicGeometry.AlgebraicStack.RelativeIsom
open FiberedCategoryOver.Groupoids Functor Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped Bicategory CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {U : AlgebraicSpace S}

/-- The action groupoid of the trivial action of `Isom_X(x, x)` on `U`. -/
def trivialActionGroupoid (x : U.toGroupoids ⟶ X) : GroupoidAlgebraicSpace U :=
  ofAction (autGroup x) (trivialAction (autGroup x))

/-- The quotient stack `[U/G]` of the trivial action of `G = Isom_X(x, x)` on
`U`. -/
abbrev trivialQuotient (x : U.toGroupoids ⟶ X) : GroupoidsOver S :=
  (SmallQuotient.quotientStack (trivialActionGroupoid x))

/-- `trivialQuotient x` is the quotient stack of the trivial-action groupoid of
`autGroup x`. -/
theorem trivialQuotient_eq (x : U.toGroupoids ⟶ X) :
    trivialQuotient x =
      SmallQuotient.quotientStack (ofAction (autGroup x) (trivialAction (autGroup x))) := sorry

/-- A co-Grothendieck object of `[U /ₚ G]` as a `T`-valued point of `U`. -/
private def trivialQuotientPoint (x : U.toGroupoids ⟶ X)
    (a : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total) :
    ((trivialActionGroupoid x).U.left).functorOfPoints.obj (op a.base) :=
  a.fiber

/-- The image of a co-Grothendieck object of `[U /ₚ G]` in the fibre of `X`. -/
private def xCanPreObjFiber (x : U.toGroupoids ⟶ X)
    (a : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total) :
    X.p.Fiber a.base :=
  (fiberFunctor x a.base).obj
    (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints a.base
      (trivialQuotientPoint x a))

/-- The fibre component of a co-Grothendieck arrow of `[U /ₚ G]` as a morphism
of functor-of-points. -/
private def xCanPreFiberHom (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (trivialActionGroupoid x).FunctorPointHom
      (trivialQuotientPoint x a)
      ((trivialActionGroupoid x).U.left.functorOfPoints.map φ.base.op
        (trivialQuotientPoint x b)) :=
  φ.fiber

/-- The `G`-valued point underlying `φ.fiber`, obtained by projecting the
trivial-action arrow space `G.X ⊗ 𝟙_ (Over U)` onto `G.X = autSpace x`. -/
private def xCanPreAutPoint (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (autSpace x).functorOfPoints.obj (op a.base) :=
  (fst (autGroup x).X (𝟙_ (Over U))).left.app (op a.base)
    (xCanPreFiberHom x φ).arrow

/-- The fibre object of `Isom_X(x, x)` classified by `φ.fiber`, via `autEquiv`. -/
private def xCanPreIsomFiber (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (relativeAut (baseProjection.{u + 1, u, u + 1} X) x).p.Fiber a.base :=
  (fiberFunctor (autEquiv x).inv a.base).obj
    (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber (autSpace x).functorOfPoints a.base
      (xCanPreAutPoint x φ))

/-- The `U`-point underlying the `Isom_X(x, x)` object of `φ.fiber`. -/
private def xCanPreIsomUPoint (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    U.toGroupoids.p.Fiber a.base :=
  (fiberFunctor (fst (baseProjection.{u + 1, u, u + 1} X) x) a.base).obj
    (xCanPreIsomFiber x φ)

/-- The `U`-point of `φ.fiber` as an automorphism of `x` is the presented source. -/
private theorem xCanPreIsomUPoint_eq_source (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ = FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints a.base
      (trivialQuotientPoint x a) := sorry

/-- The `U`-point of `φ.fiber` as an automorphism of `x` is the selected
reindexing of the presented target. -/
private theorem xCanPreIsomUPoint_eq_reindex (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ =
      Chosen.reindexObj U.toGroupoids.p φ.base
        (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints b.base
          (trivialQuotientPoint x b)) := sorry

/-- The comparison isomorphism of the `Isom_X(x, x)` fibre object of `φ`. -/
private def xCanPreComparisonIso (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (toFunctor x).obj
        (BasedCategory.PseudoPullback.fstObj (xCanPreIsomFiber x φ).1) ≅
      (toFunctor
          (FiberedCategoryOver.Groupoids.RelativeInertia.forget.{u + 1, u, u, u + 1}
            (baseProjection.{u + 1, u, u + 1} X))).obj
        (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1) :=
  BasedCategory.PseudoPullback.comparisonIsoApp (xCanPreIsomFiber x φ).1

/-- Conjugated inertia arrows satisfy the first inverse identity. -/
private theorem Implementation.xCanPreAutIso_hom_inv_id (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    ((xCanPreComparisonIso x φ).hom ≫
      (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.hom ≫
        (xCanPreComparisonIso x φ).inv) ≫
      ((xCanPreComparisonIso x φ).hom ≫
      (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.inv ≫
        (xCanPreComparisonIso x φ).inv) = 𝟙 ((toFunctor x).obj
        (BasedCategory.PseudoPullback.fstObj (xCanPreIsomFiber x φ).1)) := sorry

/-- Conjugated inertia arrows satisfy the second inverse identity. -/
private theorem Implementation.xCanPreAutIso_inv_hom_id (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    ((xCanPreComparisonIso x φ).hom ≫
      (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.inv ≫
        (xCanPreComparisonIso x φ).inv) ≫
      ((xCanPreComparisonIso x φ).hom ≫
      (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.hom ≫
        (xCanPreComparisonIso x φ).inv) = 𝟙 ((toFunctor x).obj
        (BasedCategory.PseudoPullback.fstObj (xCanPreIsomFiber x φ).1)) := sorry

/-- The total automorphism of `x` classified by `φ.fiber`. -/
private def xCanPreAutIso (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (toFunctor x).obj
        (BasedCategory.PseudoPullback.fstObj (xCanPreIsomFiber x φ).1) ≅
      (toFunctor x).obj
        (BasedCategory.PseudoPullback.fstObj (xCanPreIsomFiber x φ).1) where
  hom :=
    (xCanPreComparisonIso x φ).hom ≫
      (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.hom ≫
        (xCanPreComparisonIso x φ).inv
  inv :=
    (xCanPreComparisonIso x φ).hom ≫
      (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.inv ≫
        (xCanPreComparisonIso x φ).inv
  hom_inv_id := Implementation.xCanPreAutIso_hom_inv_id x φ
  inv_hom_id := Implementation.xCanPreAutIso_inv_hom_id x φ

/-- The hom arrow of the conjugated inertia automorphism lies over the identity. -/
private theorem Implementation.xCanPreFiberAut_hom_over (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    X.p.IsHomLift (𝟙 a.base) (xCanPreAutIso x φ).hom := sorry

/-- The inv arrow of the conjugated inertia automorphism lies over the identity. -/
private theorem Implementation.xCanPreFiberAut_inv_over (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    X.p.IsHomLift (𝟙 a.base) (xCanPreAutIso x φ).inv := sorry

/-- The vertical inertia arrows satisfy the first inverse identity. -/
private theorem Implementation.xCanPreFiberAut_hom_inv_id (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (⟨(xCanPreAutIso x φ).hom, Implementation.xCanPreFiberAut_hom_over x φ⟩ :
      (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) ⟶
        (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ)) ≫
      (⟨(xCanPreAutIso x φ).inv, Implementation.xCanPreFiberAut_inv_over x φ⟩ :
        (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) ⟶
          (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ)) =
      𝟙 ((fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ)) := sorry

/-- The vertical inertia arrows satisfy the second inverse identity. -/
private theorem Implementation.xCanPreFiberAut_inv_hom_id (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (⟨(xCanPreAutIso x φ).inv, Implementation.xCanPreFiberAut_inv_over x φ⟩ :
      (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) ⟶
        (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ)) ≫
      (⟨(xCanPreAutIso x φ).hom, Implementation.xCanPreFiberAut_hom_over x φ⟩ :
        (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) ⟶
          (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ)) =
      𝟙 ((fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ)) := sorry

/-- Fibrewise automorphism of `x` at the `U`-point of `φ.fiber`. -/
private def xCanPreFiberAut (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) ≅
      (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) where
  hom := ⟨(xCanPreAutIso x φ).hom, Implementation.xCanPreFiberAut_hom_over x φ⟩
  inv := ⟨(xCanPreAutIso x φ).inv, Implementation.xCanPreFiberAut_inv_over x φ⟩
  hom_inv_id := Implementation.xCanPreFiberAut_hom_inv_id x φ
  inv_hom_id := Implementation.xCanPreFiberAut_inv_hom_id x φ

/-- The `U`-point of `φ.fiber` identifies with the presented source. -/
private def xCanPreSourceIso (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ ≅ FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints a.base
      (trivialQuotientPoint x a) :=
  eqToIso (xCanPreIsomUPoint_eq_source x φ)

/-- The `U`-point of `φ.fiber` identifies with the selected reindexing of the
presented target. -/
private def xCanPreTargetUIso (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ ≅
      Chosen.reindexObj U.toGroupoids.p φ.base
        (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints b.base
          (trivialQuotientPoint x b)) :=
  eqToIso (xCanPreIsomUPoint_eq_reindex x φ)

/-- The switched comparison isomorphism `α : x(φ.base⁎ b) ≅ x(a)` obtained by
transporting the inverse inertia automorphism of `φ.fiber` to the presented objects of
`U`. -/
private def xCanPreAlpha (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (fiberFunctor x a.base).obj
        (Chosen.reindexObj U.toGroupoids.p φ.base
          (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints b.base
          (trivialQuotientPoint x b))) ≅
      xCanPreObjFiber x a :=
  ((fiberFunctor x a.base).mapIso (xCanPreTargetUIso x φ)).symm ≪≫
    (xCanPreFiberAut x φ).symm ≪≫
    (fiberFunctor x a.base).mapIso (xCanPreSourceIso x φ)

/-- The switched comparison triple `(b, a, α)` on presented objects of `U`. -/
private def xCanPreSwitched (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (fiberFunctor x a.base) ⊡ (fiberFunctor x a.base) :=
  ofSwitchedComparison x
    (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints a.base
      (trivialQuotientPoint x a))
    (Chosen.reindexObj U.toGroupoids.p φ.base
      (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints b.base
          (trivialQuotientPoint x b)))
    (xCanPreAlpha x φ)

/-- Selected-cleavage comparison `φ.base⁎ (x(b)) ≅ x(φ.base⁎ b)` for `x`. -/
private def xCanPreReindexIso (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    Chosen.reindexObj X.p φ.base (xCanPreObjFiber x b) ≅
      (fiberFunctor x a.base).obj
        (Chosen.reindexObj U.toGroupoids.p φ.base
          (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints b.base
          (trivialQuotientPoint x b))) :=
  CartesianBasedFunctor.Reindex.mapIso (toCartesianBasedFunctor x)
    (Cleavage.ofIsFibered U.toGroupoids.p) (Cleavage.ofIsFibered X.p) φ.base
    (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber U.functorOfPoints b.base
          (trivialQuotientPoint x b))

/-- The vertical image of a co-Grothendieck fibre: `canonicalHom` of the
switched comparison of `φ.fiber`, composed with the reindexing comparison of
`x`. -/
private def xCanPreVertical (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (xCanPreObjFiber x a).1 ⟶
      (Chosen.reindexObj X.p φ.base (xCanPreObjFiber x b)).1 :=
  (canonicalHom x (xCanPreSwitched x φ)).1 ≫ (xCanPreReindexIso x φ).inv.1

/-- The explicit total-category arrow assignment preserves identities. -/
private theorem Implementation.xCanPreTotal_map_id (x : U.toGroupoids ⟶ X)
    (a : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total) :
    xCanPreVertical x (𝟙 a) ≫
      Chosen.cartesianHom X.p (𝟙 a.base) (xCanPreObjFiber x a) =
      𝟙 (xCanPreObjFiber x a).1 := sorry

/-- The explicit total-category arrow assignment preserves composition. -/
private theorem Implementation.xCanPreTotal_map_comp (x : U.toGroupoids ⟶ X)
    {a b c : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) (ψ : b ⟶ c) :
    xCanPreVertical x (φ ≫ ψ) ≫
      Chosen.cartesianHom X.p (φ ≫ ψ).base (xCanPreObjFiber x c) =
      (xCanPreVertical x φ ≫
        Chosen.cartesianHom X.p φ.base (xCanPreObjFiber x b)) ≫
      (xCanPreVertical x ψ ≫
        Chosen.cartesianHom X.p ψ.base (xCanPreObjFiber x c)) := sorry

/-- The total-category functor of the prestack map `[U /ₚ G] ⟶ X` induced by
`x`. On objects it sends a `T`-point of `U` to `x` of the corresponding
object. On a co-Grothendieck arrow `φ` it sends `φ.fiber` through `autEquiv`
as a vertical automorphism of `x`, then composes with the selected cartesian
lift of `φ.base`. -/
private def xCanPreTotal (x : U.toGroupoids ⟶ X) :
    (SmallQuotient.preQuotient (trivialActionGroupoid x)).total ⥤ X.total where
  obj a := (xCanPreObjFiber x a).1
  map {a b} φ :=
    xCanPreVertical x φ ≫
      Chosen.cartesianHom X.p φ.base (xCanPreObjFiber x b)
  map_id := Implementation.xCanPreTotal_map_id x
  map_comp := Implementation.xCanPreTotal_map_comp x

/-- On morphisms, `xCanPreTotal` composes the vertical `canonicalHom` image of
`φ.fiber` with the selected cartesian lift of `φ.base`. -/
private theorem xCanPreTotal_map_eq (x : U.toGroupoids ⟶ X)
    {a b : (SmallQuotient.preQuotient (trivialActionGroupoid x)).total} (φ : a ⟶ b) :
    (xCanPreTotal x).map φ =
      (canonicalHom x (xCanPreSwitched x φ)).1 ≫
        (xCanPreReindexIso x φ).inv.1 ≫
        Chosen.cartesianHom X.p φ.base (xCanPreObjFiber x b) := sorry

/-- The prestack map `[U /ₚ G] ⟶ X` commutes strictly with the projections to
`Over S`. -/
private theorem xCanPreTotal_w (x : U.toGroupoids ⟶ X) :
    xCanPreTotal x ⋙ X.p = (SmallQuotient.preQuotient (trivialActionGroupoid x)).p := sorry

/-- The 1-morphism `[U /ₚ G] ⟶ X` induced by `x`. -/
def xCanPre (x : U.toGroupoids ⟶ X) :
    (SmallQuotient.preQuotient (trivialActionGroupoid x)) ⟶ X :=
  ofBasedFunctor
    { toFunctor := xCanPreTotal x
      w := xCanPreTotal_w x }

/-- The cartesian based functor underlying `xCanPre`. -/
def xCanPreCartesian (x : U.toGroupoids ⟶ X) :
    CartesianBasedFunctor ((SmallQuotient.preQuotient (trivialActionGroupoid x)).p) X.p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (xCanPreTotal x) (xCanPreTotal_w x))

/-- The selected stackification lift of `xCanPre` through
`[U /ₚ G] ⟶ [U / G]`. -/
def xCanLift (x : U.toGroupoids ⟶ X) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (SmallQuotient.stackificationPresentation (trivialActionGroupoid x)).comparison)
      (xCanPreCartesian x) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (SmallQuotient.stackificationPresentation (trivialActionGroupoid x)).isStackification
    (xCanPreCartesian x)

/-- The canonical 1-morphism `x_can : [U/G] ⟶ X` of stacks in groupoids over
`(Sch/S)_fppf` induced by a section of `π`. -/
def xCan (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    trivialQuotient x ⟶ X :=
  have := hx
  ofBasedFunctor
    (CartesianBasedFunctor.toBasedFunctor (xCanLift x).lift)

/-- `xCan` is the groupoid-fibred morphism associated to the selected
stackification lift of `xCanPre`. -/
theorem xCan_eq (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    toBasedFunctor (xCan π x hx) =
      CartesianBasedFunctor.toBasedFunctor (xCanLift x).lift := sorry

/-- After presenting `U`, the atlas triangle identifies `x` with
`atlas ≫ xCan`. -/
theorem xCan_atlas_iso (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    Nonempty (SmallQuotient.atlas (trivialActionGroupoid x) ≫ xCan π x hx ≅ x) := sorry

/-- The canonical 1-morphism `x_can : [U/G] ⟶ X` is fully faithful. -/
theorem xCan_fullyFaithful (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    Nonempty (toBasedFunctor (xCan π x hx)).FullyFaithful := sorry

end AlgebraicGeometry.AlgebraicStack
