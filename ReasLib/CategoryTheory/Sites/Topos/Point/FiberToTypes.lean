/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Point.FromSite
public import ReasLib.CategoryTheory.Sites.Types.Point

/-!
# Factoring a site point through the canonical type site

The fiber functor of a point is continuous for the jointly-surjective topology
on `Type`. This module packages the resulting morphism of topoi and its
comparison with the point obtained directly from the site point. The
continuity and left-exactness assertions are separate Prop-valued interfaces;
all point, functor, and isomorphism data remain explicit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor

universe u v w

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.FiberToTypes

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The fiber functor of a site point preserves covering families for the canonical
jointly-surjective topology on `Type`. -/
theorem coverPreserving (p : Point.{w} J) :
    CoverPreserving J typesGrothendieckTopology p.fiber := sorry

/-- The fiber functor of a site point preserves compatibility of matching families for the
canonical topology on `Type`. -/
theorem compatiblePreserving (p : Point.{w} J) :
    CompatiblePreserving typesGrothendieckTopology p.fiber := sorry

/-- The fiber functor of a site point is continuous for the canonical topology on `Type`. -/
instance isContinuous (p : Point.{w} J) :
    Functor.IsContinuous p.fiber J typesGrothendieckTopology := sorry

/-- The type-site realization, followed by direct image along a point fiber, is the skyscraper
presheaf functor of that point. -/
noncomputable def presheafIso (p : Point.{w} J) :
    typeEquiv.{w}.functor ⋙ sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
        (Functor.whiskeringLeft _ _ _).obj p.fiber.op ≅
      p.skyscraperSheafFunctor ⋙ sheafToPresheaf J (Type w) :=
  Functor.isoWhiskerRight TypesPoint.skyscraperSheafFunctorIso
    (sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
      (Functor.whiskeringLeft _ _ _).obj p.fiber.op)

/-- On presheaves, the canonical type-site realization of `E`, pulled back along a point fiber,
is the skyscraper presheaf with fiber `E`. -/
noncomputable def presheafObjIso (p : Point.{w} J) (E : Type w) :
    p.fiber.op ⋙ ((typeEquiv.{w}.functor).obj E).obj ≅ p.skyscraperPresheaf E :=
  (presheafIso p).app E

/-- The presheaf comparison used to lift the type-site realization through the fully faithful
sheaf-to-presheaf functor. -/
noncomputable def pushforwardPresheafComparison (p : Point.{w} J) :
    typeEquiv.{w}.functor ⋙ p.fiber.sheafPushforwardContinuous (Type w) J
        typesGrothendieckTopology ⋙ sheafToPresheaf J (Type w) ≅
      typeEquiv.{w}.functor ⋙ sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
        (Functor.whiskeringLeft _ _ _).obj p.fiber.op :=
  Functor.isoWhiskerLeft typeEquiv.{w}.functor
    (p.fiber.sheafPushforwardContinuousCompSheafToPresheafIso
      (Type w) J typesGrothendieckTopology)

/-- Direct image along a point fiber sends the canonical type-site realization of a type to the
skyscraper sheaf of the point. -/
noncomputable def pushforwardIso (p : Point.{w} J) :
    typeEquiv.{w}.functor ⋙ p.fiber.sheafPushforwardContinuous (Type w) J
        typesGrothendieckTopology ≅
      p.skyscraperSheafFunctor :=
  ((fullyFaithfulSheafToPresheaf J (Type w)).whiskeringRight (Type w)).preimageIso
    (pushforwardPresheafComparison p ≪≫ presheafIso p)

/-- Pullback along a point fiber is left exact for the canonical type site. -/
instance sheafPullback_preservesFiniteLimits
    (p : Point.{w} J) [HasWeakSheafify typesGrothendieckTopology (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, p.fiber.op.HasLeftKanExtension P] :
    PreservesFiniteLimits (p.fiber.sheafPullback (Type w) J typesGrothendieckTopology) := sorry

/-- The morphism of topoi induced by the fiber of a site point and the canonical type site. -/
@[stacks 04EL "(2)"]
noncomputable def morphism
    (p : Point.{w} J) [HasWeakSheafify typesGrothendieckTopology (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, p.fiber.op.HasLeftKanExtension P] :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} :=
  p.fiber.morphismOfTopoiInOfContinuous J typesGrothendieckTopology

/-- Lemma 7.32.8: after presenting the terminal topos by the canonical type site, the point
obtained from the fiber of `p` has the same direct image as `p.toToposPoint`. -/
@[stacks 04EL "(3)"]
noncomputable def typePushforwardIso
    (p : Point.{w} J) [LocallySmall.{w} C]
    [HasWeakSheafify typesGrothendieckTopology (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, p.fiber.op.HasLeftKanExtension P] :
    (morphism p).typePushforward ≅ p.toToposPoint.typePushforward :=
  pushforwardIso p ≪≫ (p.toToposPoint_pointPushforwardIso).symm

/-- The inverse image of the fiber-induced point agrees with the inverse image of the point
constructed directly from the site point. -/
noncomputable def typeInverseImageIso
    (p : Point.{w} J) [LocallySmall.{w} C]
    [HasWeakSheafify typesGrothendieckTopology (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, p.fiber.op.HasLeftKanExtension P] :
    (morphism p).typeInverseImage ≅ p.toToposPoint.typeInverseImage :=
  Adjunction.leftAdjointUniq (morphism p).typeAdjunction
    (p.toToposPoint.typeAdjunction.ofNatIsoRight (typePushforwardIso p).symm)

end CategoryTheory.GrothendieckTopology.Point.FiberToTypes
