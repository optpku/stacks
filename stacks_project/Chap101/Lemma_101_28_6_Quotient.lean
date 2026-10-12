/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import stacks_project.Chap78.Lemma_78_27_2_TrivialAction
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.«94_16_1_1_CanonicalHom»
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import stacks_project.Chap101.Lemma_101_28_6_Aut

/-!
# Canonical 1-morphism from a trivial-action quotient stack

A section `x : U ⟶ X` of a morphism of algebraic stacks determines a canonical
1-morphism `xCan` from the quotient stack `[U/G]` of the trivial action of
`G = Isom_X(x, x)` to `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace AlgebraicGeometry.GroupAlgebraicSpace
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
  (trivialActionGroupoid x).quotientStack

/-- `trivialQuotient x` is the quotient stack of the trivial-action groupoid of
`autGroup x`. -/
theorem trivialQuotient_eq (x : U.toGroupoids ⟶ X) :
    trivialQuotient x =
      (ofAction (autGroup x) (trivialAction (autGroup x))).quotientStack :=
  sorry

/-- A co-Grothendieck object of `[U /ₚ G]` as a `T`-valued point of `U`. -/
def trivialQuotientPoint (x : U.toGroupoids ⟶ X)
    (a : (trivialActionGroupoid x).preQuotient.total) :
    ((trivialActionGroupoid x).U.left).functorOfPoints.obj (op a.base) :=
  a.fiber

/-- `trivialQuotientPoint` is the object-space point underlying a
co-Grothendieck object of `[U /ₚ G]`. -/
theorem trivialQuotientPoint_eq (x : U.toGroupoids ⟶ X)
    (a : (trivialActionGroupoid x).preQuotient.total) :
    trivialQuotientPoint x a = a.fiber :=
  sorry

/-- The image of a co-Grothendieck object of `[U /ₚ G]` in the fibre of `X`. -/
def xCanPreObjFiber (x : U.toGroupoids ⟶ X)
    (a : (trivialActionGroupoid x).preQuotient.total) :
    X.p.Fiber a.base :=
  (fiberFunctor x a.base).obj
    (pointAsPresentedFiber (trivialQuotientPoint x a))

/-- `xCanPreObjFiber` applies `x` to the presented object-space point. -/
theorem xCanPreObjFiber_eq (x : U.toGroupoids ⟶ X)
    (a : (trivialActionGroupoid x).preQuotient.total) :
    xCanPreObjFiber x a =
      (fiberFunctor x a.base).obj
        (pointAsPresentedFiber (trivialQuotientPoint x a)) :=
  sorry

/-- The fibre component of a co-Grothendieck arrow of `[U /ₚ G]` as a morphism
of functor-of-points. -/
def xCanPreFiberHom (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (trivialActionGroupoid x).FunctorPointHom
      (trivialQuotientPoint x a)
      ((trivialActionGroupoid x).U.left.functorOfPoints.map φ.base.op
        (trivialQuotientPoint x b)) :=
  φ.fiber

/-- `xCanPreFiberHom` is the fibre component of the co-Grothendieck arrow. -/
theorem xCanPreFiberHom_eq (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreFiberHom x φ = φ.fiber :=
  sorry

/-- The `G`-valued point underlying `φ.fiber`, obtained by projecting the
trivial-action arrow space `G.X ⊗ 𝟙_ (Over U)` onto `G.X = autSpace x`. -/
def xCanPreAutPoint (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (autSpace x).functorOfPoints.obj (op a.base) :=
  (fst (autGroup x).X (𝟙_ (Over U))).left.app (op a.base)
    (xCanPreFiberHom x φ).arrow

/-- `xCanPreAutPoint` is the group-component projection of `φ.fiber`. -/
theorem xCanPreAutPoint_eq (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreAutPoint x φ =
      (fst (autGroup x).X (𝟙_ (Over U))).left.app (op a.base)
        (xCanPreFiberHom x φ).arrow :=
  sorry

/-- The fibre object of `Isom_X(x, x)` classified by `φ.fiber`, via `autEquiv`. -/
def xCanPreIsomFiber (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (relativeAut (baseProjection.{u + 1, u, u + 1} X) x).p.Fiber a.base :=
  (fiberFunctor (autEquiv x).inv a.base).obj
    (pointAsPresentedFiber (xCanPreAutPoint x φ))

/-- `xCanPreIsomFiber` applies `autEquiv.inv` to the presented `G`-point. -/
theorem xCanPreIsomFiber_eq (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreIsomFiber x φ =
      (fiberFunctor (autEquiv x).inv a.base).obj
        (pointAsPresentedFiber (xCanPreAutPoint x φ)) :=
  sorry

/-- The `U`-point underlying the `Isom_X(x, x)` object of `φ.fiber`. -/
def xCanPreIsomUPoint (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    U.toGroupoids.p.Fiber a.base :=
  (fiberFunctor (fst (baseProjection.{u + 1, u, u + 1} X) x) a.base).obj
    (xCanPreIsomFiber x φ)

/-- `xCanPreIsomUPoint` is the first projection of `xCanPreIsomFiber`. -/
theorem xCanPreIsomUPoint_eq (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ =
      (fiberFunctor (fst (baseProjection.{u + 1, u, u + 1} X) x) a.base).obj
        (xCanPreIsomFiber x φ) :=
  sorry

/-- The `U`-point of `φ.fiber` as an automorphism of `x` is the presented source. -/
theorem xCanPreIsomUPoint_eq_source (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ = pointAsPresentedFiber (trivialQuotientPoint x a) :=
  sorry

/-- The `U`-point of `φ.fiber` as an automorphism of `x` is the selected
reindexing of the presented target. -/
theorem xCanPreIsomUPoint_eq_reindex (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ =
      Chosen.reindexObj U.toGroupoids.p φ.base
        (pointAsPresentedFiber (trivialQuotientPoint x b)) :=
  sorry

/-- The comparison isomorphism of the `Isom_X(x, x)` fibre object of `φ`. -/
def xCanPreComparisonIso (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor x).obj
        (BasedCategory.PseudoPullback.fstObj (xCanPreIsomFiber x φ).1) ≅
      (toFunctor
          (FiberedCategoryOver.Groupoids.RelativeInertia.forget.{u + 1, u, u, u + 1}
            (baseProjection.{u + 1, u, u + 1} X))).obj
        (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1) :=
  BasedCategory.PseudoPullback.comparisonIsoApp (xCanPreIsomFiber x φ).1

/-- `xCanPreComparisonIso` is the objectwise pseudo-pullback comparison of
`xCanPreIsomFiber`. -/
theorem xCanPreComparisonIso_eq (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreComparisonIso x φ =
      BasedCategory.PseudoPullback.comparisonIsoApp (xCanPreIsomFiber x φ).1 :=
  sorry

/-- The total automorphism of `x` classified by `φ.fiber`. -/
def xCanPreAutIso (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
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
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `xCanPreAutIso` conjugates the inertia automorphism of `φ.fiber` along the
comparison isomorphism of `Isom_X(x, x)`. -/
theorem xCanPreAutIso_hom (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (xCanPreAutIso x φ).hom =
      (xCanPreComparisonIso x φ).hom ≫
        (BasedCategory.PseudoPullback.sndObj (xCanPreIsomFiber x φ).1).aut.hom ≫
          (xCanPreComparisonIso x φ).inv :=
  sorry

/-- Fibrewise automorphism of `x` at the `U`-point of `φ.fiber`. -/
def xCanPreFiberAut (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) ≅
      (fiberFunctor x a.base).obj (xCanPreIsomUPoint x φ) where
  hom := ⟨(xCanPreAutIso x φ).hom, sorry⟩
  inv := ⟨(xCanPreAutIso x φ).inv, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The `U`-point of `φ.fiber` identifies with the presented source. -/
def xCanPreSourceIso (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ ≅ pointAsPresentedFiber (trivialQuotientPoint x a) :=
  eqToIso (xCanPreIsomUPoint_eq_source x φ)

/-- The `U`-point of `φ.fiber` identifies with the selected reindexing of the
presented target. -/
def xCanPreTargetUIso (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    xCanPreIsomUPoint x φ ≅
      Chosen.reindexObj U.toGroupoids.p φ.base
        (pointAsPresentedFiber (trivialQuotientPoint x b)) :=
  eqToIso (xCanPreIsomUPoint_eq_reindex x φ)

/-- The switched comparison isomorphism `α : x(φ.base⁎ b) ≅ x(a)` obtained by
transporting the inertia automorphism of `φ.fiber` to the presented objects of
`U`. -/
def xCanPreAlpha (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor x a.base).obj
        (Chosen.reindexObj U.toGroupoids.p φ.base
          (pointAsPresentedFiber (trivialQuotientPoint x b))) ≅
      xCanPreObjFiber x a :=
  ((fiberFunctor x a.base).mapIso (xCanPreTargetUIso x φ)).symm ≪≫
    xCanPreFiberAut x φ ≪≫
    (fiberFunctor x a.base).mapIso (xCanPreSourceIso x φ)

/-- The switched comparison triple `(b, a, α)` on presented objects of `U`. -/
def xCanPreSwitched (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (fiberFunctor x a.base) ⊡ (fiberFunctor x a.base) :=
  ofSwitchedComparison x
    (pointAsPresentedFiber (trivialQuotientPoint x a))
    (Chosen.reindexObj U.toGroupoids.p φ.base
      (pointAsPresentedFiber (trivialQuotientPoint x b)))
    (xCanPreAlpha x φ)

/-- Selected-cleavage comparison `φ.base⁎ (x(b)) ≅ x(φ.base⁎ b)` for `x`. -/
def xCanPreReindexIso (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    Chosen.reindexObj X.p φ.base (xCanPreObjFiber x b) ≅
      (fiberFunctor x a.base).obj
        (Chosen.reindexObj U.toGroupoids.p φ.base
          (pointAsPresentedFiber (trivialQuotientPoint x b))) :=
  CartesianBasedFunctor.Reindex.mapIso
    (toCartesianBasedFunctor x)
    (Cleavage.ofIsFibered U.toGroupoids.p)
    (Cleavage.ofIsFibered X.p) φ.base
    (pointAsPresentedFiber (trivialQuotientPoint x b))

/-- The vertical image of a co-Grothendieck fibre: `canonicalHom` of the
switched comparison of `φ.fiber`, composed with the reindexing comparison of
`x`. -/
def xCanPreVertical (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (xCanPreObjFiber x a).1 ⟶
      (Chosen.reindexObj X.p φ.base (xCanPreObjFiber x b)).1 :=
  (canonicalHom x (xCanPreSwitched x φ)).1 ≫ (xCanPreReindexIso x φ).inv.1

/-- The total-category functor of the prestack map `[U /ₚ G] ⟶ X` induced by
`x`. On objects it sends a `T`-point of `U` to `x` of the corresponding
object. On a co-Grothendieck arrow `φ` it sends `φ.fiber` through `autEquiv`
as a vertical automorphism of `x`, then composes with the selected cartesian
lift of `φ.base`. -/
def xCanPreTotal (x : U.toGroupoids ⟶ X) :
    (trivialActionGroupoid x).preQuotient.total ⥤ X.total where
  obj a := (xCanPreObjFiber x a).1
  map {a b} φ :=
    xCanPreVertical x φ ≫
      Chosen.cartesianHom X.p φ.base (xCanPreObjFiber x b)
  map_id := sorry
  map_comp := sorry

/-- On morphisms, `xCanPreTotal` composes the vertical `canonicalHom` image of
`φ.fiber` with the selected cartesian lift of `φ.base`. -/
theorem xCanPreTotal_map_eq (x : U.toGroupoids ⟶ X)
    {a b : (trivialActionGroupoid x).preQuotient.total} (φ : a ⟶ b) :
    (xCanPreTotal x).map φ =
      (canonicalHom x (xCanPreSwitched x φ)).1 ≫
        (xCanPreReindexIso x φ).inv.1 ≫
        Chosen.cartesianHom X.p φ.base (xCanPreObjFiber x b) :=
  sorry

/-- The prestack map `[U /ₚ G] ⟶ X` commutes strictly with the projections to
`Over S`. -/
theorem xCanPreTotal_w (x : U.toGroupoids ⟶ X) :
    xCanPreTotal x ⋙ X.p = (trivialActionGroupoid x).preQuotient.p :=
  sorry

/-- The 1-morphism `[U /ₚ G] ⟶ X` induced by `x`. -/
def xCanPre (x : U.toGroupoids ⟶ X) :
    (trivialActionGroupoid x).preQuotient ⟶ X :=
  ofBasedFunctor
    { toFunctor := xCanPreTotal x
      w := xCanPreTotal_w x }

/-- `xCanPre` is the groupoid-fibred morphism associated to `xCanPreTotal`. -/
theorem xCanPre_eq (x : U.toGroupoids ⟶ X) :
    toFunctor (xCanPre x) = xCanPreTotal x :=
  sorry

/-- The cartesian based functor underlying `xCanPre`. -/
def xCanPreCartesian (x : U.toGroupoids ⟶ X) :
    CartesianBasedFunctor ((trivialActionGroupoid x).preQuotient.p) X.p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (xCanPreTotal x) (xCanPreTotal_w x))

/-- `xCanPreCartesian` is the cartesian based functor associated to
`xCanPreTotal`. -/
theorem xCanPreCartesian_eq (x : U.toGroupoids ⟶ X) :
    (xCanPreCartesian x).toBasedFunctor =
      BasedFunctor.ofFunctor (xCanPreTotal x) (xCanPreTotal_w x) :=
  sorry

/-- The selected stackification lift of `xCanPre` through
`[U /ₚ G] ⟶ [U / G]`. -/
def xCanLift (x : U.toGroupoids ⟶ X) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (trivialActionGroupoid x).stackificationPresentation.comparison)
      (xCanPreCartesian x) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (trivialActionGroupoid x).stackificationPresentation.isStackification
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
      CartesianBasedFunctor.toBasedFunctor (xCanLift x).lift :=
  sorry

/-- The atlas composite of `xCan`. -/
def xCan_atlas (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    (trivialActionGroupoid x).U.left.toGroupoids ⟶ X :=
  (trivialActionGroupoid x).atlas ≫ xCan π x hx

/-- `xCan_atlas` is the composite of the quotient atlas with `xCan`. -/
theorem xCan_atlas_eq (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    xCan_atlas π x hx = (trivialActionGroupoid x).atlas ≫ xCan π x hx :=
  sorry

/-- After presenting `U`, the atlas triangle identifies `x` with
`atlas ≫ xCan`. -/
theorem xCan_atlas_iso (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    Nonempty (xCan_atlas π x hx ≅ x) :=
  sorry

/-- The canonical 1-morphism `x_can : [U/G] ⟶ X` is fully faithful. -/
theorem xCan_fullyFaithful (π : X ⟶ U.toGroupoids) (x : U.toGroupoids ⟶ X)
    (hx : x ≫ π ≅ 𝟙 U.toGroupoids) :
    Nonempty (toBasedFunctor (xCan π x hx)).FullyFaithful :=
  sorry

end AlgebraicGeometry.AlgebraicStack
