module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Points.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Basic
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian

/-!
# Functoriality of quotient stacks

A morphism of groupoids in algebraic spaces induces a cartesian morphism of
their point prestacks. The universal property of stackification extends this
morphism to the fppf quotient stacks, with an invertible comparison cell.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

private theorem pointsMapStrongTrans_naturality (f : Hom G H)
    {T T' : LocallyDiscrete (Over S)ᵒᵖ} (g : T ⟶ T') :
    (G.points ⋙ Grpd.forgetToCat).toPseudofunctor'.map g ≫
        Grpd.forgetToCat.map (f.pointsMap.app T'.as) =
      Grpd.forgetToCat.map (f.pointsMap.app T.as) ≫
        (H.points ⋙ Grpd.forgetToCat).toPseudofunctor'.map g := sorry

private theorem pointsMapStrongTrans_naturality_naturality (f : Hom G H) :
    let F := (G.points ⋙ Grpd.forgetToCat).toPseudofunctor'
    let K := (H.points ⋙ Grpd.forgetToCat).toPseudofunctor'
    let app := fun T : LocallyDiscrete (Over S)ᵒᵖ ↦
      Grpd.forgetToCat.map (f.pointsMap.app T.as)
    let naturality := fun {T T' : LocallyDiscrete (Over S)ᵒᵖ} (g : T ⟶ T') ↦
      eqToIso (pointsMapStrongTrans_naturality f g)
    ∀ {a b : LocallyDiscrete (Over S)ᵒᵖ} {g h : a ⟶ b} (η : g ⟶ h),
      F.map₂ η ▷ app b ≫ (naturality h).hom =
        (naturality g).hom ≫ app a ◁ K.map₂ η := sorry

private theorem pointsMapStrongTrans_naturality_id (f : Hom G H) :
    let F := (G.points ⋙ Grpd.forgetToCat).toPseudofunctor'
    let K := (H.points ⋙ Grpd.forgetToCat).toPseudofunctor'
    let app := fun T : LocallyDiscrete (Over S)ᵒᵖ ↦
      Grpd.forgetToCat.map (f.pointsMap.app T.as)
    let naturality := fun {T T' : LocallyDiscrete (Over S)ᵒᵖ} (g : T ⟶ T') ↦
      eqToIso (pointsMapStrongTrans_naturality f g)
    ∀ a : LocallyDiscrete (Over S)ᵒᵖ,
      (naturality (𝟙 a)).hom ≫ app a ◁ (K.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := sorry

private theorem pointsMapStrongTrans_naturality_comp (f : Hom G H) :
    let F := (G.points ⋙ Grpd.forgetToCat).toPseudofunctor'
    let K := (H.points ⋙ Grpd.forgetToCat).toPseudofunctor'
    let app := fun T : LocallyDiscrete (Over S)ᵒᵖ ↦
      Grpd.forgetToCat.map (f.pointsMap.app T.as)
    let naturality := fun {T T' : LocallyDiscrete (Over S)ᵒᵖ} (g : T ⟶ T') ↦
      eqToIso (pointsMapStrongTrans_naturality f g)
    ∀ {a b c : LocallyDiscrete (Over S)ᵒᵖ} (g : a ⟶ b) (h : b ⟶ c),
      (naturality (g ≫ h)).hom ≫ app a ◁ (K.mapComp g h).hom =
        (F.mapComp g h).hom ▷ app c ≫ (α_ _ _ _).hom ≫
          F.map g ◁ (naturality h).hom ≫ (α_ _ _ _).inv ≫
          (naturality g).hom ▷ K.map h ≫ (α_ _ _ _).hom := sorry

/-- The transformation of scheme-valued point groupoids induces a strong transformation
of the associated co-Grothendieck pseudofunctors, with naturality given by equality transport. -/
def pointsMapStrongTrans (f : Hom G H) :
    (G.points ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
      (H.points ⋙ Grpd.forgetToCat).toPseudofunctor' where
  app T := Grpd.forgetToCat.map (f.pointsMap.app T.as)
  naturality := fun g ↦ eqToIso (pointsMapStrongTrans_naturality f g)
  naturality_naturality := pointsMapStrongTrans_naturality_naturality f
  naturality_id := pointsMapStrongTrans_naturality_id f
  naturality_comp := pointsMapStrongTrans_naturality_comp f

/-- The total functor of point prestacks induced by a groupoid morphism is the
co-Grothendieck map of its strong transformation of point pseudofunctors. -/
def prestackMapFunctor (f : Hom G H) :
    ∫ᶜ ((G.points ⋙ Grpd.forgetToCat).toPseudofunctor') ⥤
      ∫ᶜ ((H.points ⋙ Grpd.forgetToCat).toPseudofunctor') :=
  Pseudofunctor.CoGrothendieck.map (pointsMapStrongTrans f)

/-- A groupoid morphism induces a cartesian morphism between the prestacks of scheme points. -/
def prestackMap (f : Hom G H) :
    CartesianBasedFunctor (groupoidPresheafProjection G.points)
      (groupoidPresheafProjection H.points) :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (Pseudofunctor.CoGrothendieck.mapBased (pointsMapStrongTrans f))

/-- The morphism from the source point prestack to the target quotient stack obtained by
composing the induced prestack morphism with stackification of the target. -/
def prestackToQuotient (f : Hom G H) :
    CartesianBasedFunctor (groupoidPresheafProjection G.points) (fppfQuotientStack H).p :=
  (prestackMap f).comp (fppfQuotientStackPresentation H).comparison

/-- The selected factorization of the induced morphism to the target quotient stack
through stackification of the source point prestack. -/
def quotientStackLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation G).comparison) (prestackToQuotient f) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation G).isStackification (prestackToQuotient f)

/-- A morphism of groupoids in algebraic spaces induces a canonical cartesian morphism
between their fppf quotient stacks by the universal property of stackification. -/
def quotientStackMap (f : Hom G H) :
    CartesianBasedFunctor (fppfQuotientStack G).p (fppfQuotientStack H).p :=
  (quotientStackLift f).lift

/-- Precomposing the induced quotient-stack morphism with the source stackification
comparison recovers the morphism from the point prestack to the target quotient stack,
up to the selected invertible comparison cell. -/
def quotientStackMap_comp (f : Hom G H) :
    (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
          (fppfQuotientStackPresentation G).comparison).obj
        (quotientStackMap f) ≅ prestackToQuotient f :=
  (quotientStackLift f).comparison

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
