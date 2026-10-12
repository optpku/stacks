/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap78.Lemma_78_28_1_Quotient

/-!
# Morphisms of quotient stacks induced by morphisms of groupoids

A morphism `f : Hom G H` of groupoids in algebraic spaces over `B` induces a map of
groupoid-valued points, hence a cartesian functor of prestacks `[U/_p R] ⟶ [U'/_p R']`.
Composing with stackification of the target and lifting through stackification of the
source produces the canonical 1-morphism `[f] : [U/R] ⟶ [U'/R']`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- The functor of scheme-valued point groupoids on `(Sch/S)_fppf` induced by a morphism of
groupoids in algebraic spaces. On objects it postcomposes by `f.obj.left`; on arrows it
postcomposes by `f.arrow.left`. -/
def pointsMap {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.points ⟶ H.points where
  app T :=
    { obj := fun x ↦ x ≫ f.obj.left
      map := fun p ↦
        { arrow := p.arrow ≫ f.arrow.left
          source := sorry
          target := sorry }
      map_id := sorry
      map_comp := sorry }
  naturality := sorry

/-- On objects, `pointsMap` is postcomposition with the object map of `f`. -/
theorem pointsMap_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (T : Over S)
    (x : ofOver T ⟶ G.U.left) :
    (f.pointsMap.app (op T)).obj x = x ≫ f.obj.left := sorry

/-- On arrows, `pointsMap` is postcomposition with the arrow map of `f`. -/
theorem pointsMap_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (T : Over S)
    {x y : ofOver T ⟶ G.U.left} (p : G.SpacePointHom x y) :
    ((f.pointsMap.app (op T)).map p).arrow = p.arrow ≫ f.arrow.left := sorry

/-- The strong transformation of co-Grothendieck pseudofunctors associated to `pointsMap`.
On components it is `Grpd.forgetToCat.map` of `pointsMap`; the naturality 2-isomorphism is the
equality transport of the naturality square of `pointsMap`. -/
def pointsMapStrongTrans {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    (G.points ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
      (H.points ⋙ Grpd.forgetToCat).toPseudofunctor' where
  app T := Grpd.forgetToCat.map (f.pointsMap.app T.as)
  naturality _ := eqToIso sorry
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- The total functor of co-Grothendieck projections induced by `pointsMap`. This is
`CoGrothendieck.map` of `pointsMapStrongTrans`, so on arrows it maps the fiber component by
`pointsMap` and then composes with the naturality transport. -/
def prestackMapFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    ∫ᶜ ((G.points ⋙ Grpd.forgetToCat).toPseudofunctor') ⥤
      ∫ᶜ ((H.points ⋙ Grpd.forgetToCat).toPseudofunctor') :=
  Pseudofunctor.CoGrothendieck.map (pointsMapStrongTrans f)

/-- The cartesian 1-morphism `[U/_p R] ⟶ [U'/_p R']` induced by a morphism of groupoids. -/
def prestackMap {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : CartesianBasedFunctor (prestack G).p (prestack H).p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor (prestackMapFunctor f) sorry) sorry

/-- The composite `[U/_p R] ⟶ [U'/R']` of `prestackMap` with stackification of the target. -/
def prestackToQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    CartesianBasedFunctor (prestack G).p (fppfQuotientStack H).p :=
  (prestackMap f).comp (fppfQuotientStackPresentation H).comparison

/-- The selected stackification lift of `prestackToQuotient` through the comparison
`[U/_p R] ⟶ [U/R]`. -/
def quotientStackLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation G).comparison) (prestackToQuotient f) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation G).isStackification (prestackToQuotient f)

/-- The canonical 1-morphism `[f] : [U/R] ⟶ [U'/R']` of quotient stacks over `(Sch/S)_fppf`
induced by a morphism of groupoids in algebraic spaces. -/
def quotientStackMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    CartesianBasedFunctor (fppfQuotientStack G).p (fppfQuotientStack H).p :=
  (quotientStackLift f).lift

/-- The characterizing invertible 2-cell of the stackification universal property:
precomposing `[f]` with `[U/_p R] ⟶ [U/R]` recovers `prestackToQuotient`. -/
def quotientStackMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
          (fppfQuotientStackPresentation G).comparison).obj
        (quotientStackMap f) ≅ prestackToQuotient f :=
  (quotientStackLift f).comparison

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
