/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification

/-!
# Functoriality of small groupoid quotient stacks

A morphism of algebraic-space groupoids acts on small functor-of-points groupoids.
The induced functor on their co-Grothendieck constructions extends through stackification.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open Functor Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

/-- The image of a functor-of-points arrow has the images of its original endpoints. -/
private theorem presheafMap_endpoints (f : Hom G H) (T : (Over S)ᵒᵖ)
    {x y : G.U.left.functorOfPoints.obj T} (p : G.FunctorPointHom x y) :
    H.s.left.app T (f.arrow.left.app T p.arrow) = f.obj.left.app T x ∧
      H.t.left.app T (f.arrow.left.app T p.arrow) = f.obj.left.app T y := sorry

/-- The arrow map on functor-of-points is the arrow component of the groupoid morphism. -/
private def presheafMapArrow (f : Hom G H) (T : (Over S)ᵒᵖ)
    {x y : G.U.left.functorOfPoints.obj T} (p : G.FunctorPointHom x y) :
    H.FunctorPointHom (f.obj.left.app T x) (f.obj.left.app T y) :=
  FunctorPointHom.ofArrow (f.arrow.left.app T p.arrow)
    (presheafMap_endpoints f T p).1 (presheafMap_endpoints f T p).2

/-- The induced arrow map preserves identity arrows. -/
private theorem presheafMap_id (f : Hom G H) (T : (Over S)ᵒᵖ)
    (x : G.U.left.functorOfPoints.obj T) :
    presheafMapArrow f T (FunctorPointHom.id x) = FunctorPointHom.id (f.obj.left.app T x) := sorry

/-- The induced arrow map preserves composition of arrows. -/
private theorem presheafMap_comp (f : Hom G H) (T : (Over S)ᵒᵖ)
    {x y z : G.U.left.functorOfPoints.obj T}
    (p : G.FunctorPointHom x y) (q : G.FunctorPointHom y z) :
    presheafMapArrow f T (FunctorPointHom.comp p q) =
      FunctorPointHom.comp (presheafMapArrow f T p) (presheafMapArrow f T q) := sorry

/-- A groupoid morphism induces a functor on each small groupoid of points. -/
private def presheafMapComponent (f : Hom G H) (T : (Over S)ᵒᵖ) :
    G.groupoidPresheaf.obj T ⥤ H.groupoidPresheaf.obj T where
  obj := fun x ↦ f.obj.left.app T x
  map := presheafMapArrow f T
  map_id := presheafMap_id f T
  map_comp := presheafMap_comp f T

/-- The functors on point groupoids commute with restriction of test schemes. -/
private theorem presheafMap_naturality (f : Hom G H)
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    G.groupoidPresheaf.map g ⋙ presheafMapComponent f T' =
      presheafMapComponent f T ⋙ H.groupoidPresheaf.map g := sorry

/-- The natural transformation of small groupoid-valued points induced by a groupoid morphism. -/
def presheafMap (f : Hom G H) : G.groupoidPresheaf ⟶ H.groupoidPresheaf where
  app := presheafMapComponent f
  naturality {T T'} g := presheafMap_naturality f g

/-- The object map on functor-of-points is the object component of the groupoid morphism. -/
theorem presheafMap_obj (f : Hom G H) (T : (Over S)ᵒᵖ)
    (x : G.U.left.functorOfPoints.obj T) :
    ((presheafMap f).app T).obj x = f.obj.left.app T x := rfl

/-- Restriction commutes with the components viewed as morphisms of categories. -/
private theorem presheafStrongTrans_naturality (f : Hom G H)
    {T T' : LocallyDiscrete (Over S)ᵒᵖ} (g : T ⟶ T') :
    (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map g ≫
        Grpd.forgetToCat.map ((presheafMap f).app T'.as) =
      Grpd.forgetToCat.map ((presheafMap f).app T.as) ≫
        (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map g := sorry

/-- Equality of restriction functors gives the naturality isomorphism. -/
private def presheafStrongTransNaturality (f : Hom G H)
    {T T' : LocallyDiscrete (Over S)ᵒᵖ} (g : T ⟶ T') :
    (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map g ≫
        Grpd.forgetToCat.map ((presheafMap f).app T'.as) ≅
      Grpd.forgetToCat.map ((presheafMap f).app T.as) ≫
        (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map g :=
  eqToIso (presheafStrongTrans_naturality f g)

/-- The naturality isomorphisms respect two-morphisms of test schemes. -/
private theorem presheafStrongTrans_naturality_naturality (f : Hom G H) :
    let F := (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'
    let K := (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'
    let app := fun T : LocallyDiscrete (Over S)ᵒᵖ ↦
      Grpd.forgetToCat.map ((presheafMap f).app T.as)
    ∀ {a b : LocallyDiscrete (Over S)ᵒᵖ} {g h : a ⟶ b} (η : g ⟶ h),
      F.map₂ η ▷ app b ≫ (presheafStrongTransNaturality f h).hom =
        (presheafStrongTransNaturality f g).hom ≫ app a ◁ K.map₂ η := sorry

/-- The naturality isomorphisms respect identity morphisms of test schemes. -/
private theorem presheafStrongTrans_naturality_id (f : Hom G H) :
    let F := (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'
    let K := (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'
    let app := fun T : LocallyDiscrete (Over S)ᵒᵖ ↦
      Grpd.forgetToCat.map ((presheafMap f).app T.as)
    ∀ a : LocallyDiscrete (Over S)ᵒᵖ,
      (presheafStrongTransNaturality f (𝟙 a)).hom ≫ app a ◁ (K.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := sorry

/-- The naturality isomorphisms respect composition of test-scheme morphisms. -/
private theorem presheafStrongTrans_naturality_comp (f : Hom G H) :
    let F := (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'
    let K := (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'
    let app := fun T : LocallyDiscrete (Over S)ᵒᵖ ↦
      Grpd.forgetToCat.map ((presheafMap f).app T.as)
    ∀ {a b c : LocallyDiscrete (Over S)ᵒᵖ} (g : a ⟶ b) (h : b ⟶ c),
      (presheafStrongTransNaturality f (g ≫ h)).hom ≫ app a ◁ (K.mapComp g h).hom =
        (F.mapComp g h).hom ▷ app c ≫ (α_ _ _ _).hom ≫
          F.map g ◁ (presheafStrongTransNaturality f h).hom ≫ (α_ _ _ _).inv ≫
          (presheafStrongTransNaturality f g).hom ▷ K.map h ≫ (α_ _ _ _).hom := sorry

/-- The strong transformation of co-Grothendieck pseudofunctors induced by a groupoid morphism. -/
def presheafStrongTrans (f : Hom G H) :
    (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
      (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor' where
  app T := Grpd.forgetToCat.map ((presheafMap f).app T.as)
  naturality := presheafStrongTransNaturality f
  naturality_naturality := presheafStrongTrans_naturality_naturality f
  naturality_id := presheafStrongTrans_naturality_id f
  naturality_comp := presheafStrongTrans_naturality_comp f

/-- The total functor of co-Grothendieck projections induced by a groupoid morphism. -/
def preQuotientMapFunctor (f : Hom G H) :
    (SmallQuotient.preQuotient G).total ⥤ (SmallQuotient.preQuotient H).total :=
  Pseudofunctor.CoGrothendieck.map (presheafStrongTrans f)

/-- The total functor commutes with the projections to test schemes. -/
private theorem preQuotientMapFunctor_over (f : Hom G H) :
    preQuotientMapFunctor f ⋙ (SmallQuotient.preQuotient H).p =
      (SmallQuotient.preQuotient G).p := sorry

/-- The cartesian based functor on small groupoid prestacks induced by a groupoid morphism. -/
def preQuotientMapCartesian (f : Hom G H) :
    CartesianBasedFunctor (SmallQuotient.preQuotient G).p (SmallQuotient.preQuotient H).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (preQuotientMapFunctor f) (preQuotientMapFunctor_over f))

/-- The morphism of small groupoid prestacks induced by a groupoid morphism. -/
def preQuotientMap (f : Hom G H) :
    SmallQuotient.preQuotient G ⟶ SmallQuotient.preQuotient H :=
  ofBasedFunctor (preQuotientMapCartesian f).toBasedFunctor

/-- The prestack morphism followed by stackification of the target. -/
def preQuotientToQuotient (f : Hom G H) :
    CartesianBasedFunctor (SmallQuotient.preQuotient G).p (SmallQuotient.quotientStack H).p :=
  (preQuotientMapCartesian f).comp (SmallQuotient.stackificationPresentation H).comparison

/-- The selected extension of the prestack morphism through stackification of the source. -/
def smallQuotientStackLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (SmallQuotient.stackificationPresentation G).comparison) (preQuotientToQuotient f) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (SmallQuotient.stackificationPresentation G).isStackification
    (preQuotientToQuotient f)

/-- The induced morphism between the small stackifications of groupoid prestacks. -/
def quotientStackHom (f : Hom G H) :
    SmallQuotient.quotientStack G ⟶ SmallQuotient.quotientStack H :=
  ofBasedFunctor (CartesianBasedFunctor.toBasedFunctor (smallQuotientStackLift f).lift)

/-- The underlying based functor of the quotient morphism is its selected stackification lift. -/
theorem quotientStackHom_eq (f : Hom G H) :
    toBasedFunctor (quotientStackHom f) =
      CartesianBasedFunctor.toBasedFunctor (smallQuotientStackLift f).lift := rfl

/-- Precomposing the induced quotient morphism with stackification recovers the prestack map. -/
def quotientStackHom_comp (f : Hom G H) :
    (CartesianBasedFunctor.precomp (SmallQuotient.quotientStack H).p
          (SmallQuotient.stackificationPresentation G).comparison).obj
        (smallQuotientStackLift f).lift ≅ preQuotientToQuotient f :=
  (smallQuotientStackLift f).comparison

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
