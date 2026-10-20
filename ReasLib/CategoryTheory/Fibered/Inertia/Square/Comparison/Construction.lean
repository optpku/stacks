/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Routes.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison in the relative-inertia square

This module owns the objectwise and based natural isomorphisms comparing the
target and source routes. Their component readouts live in `Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedNatIso BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

namespace RelativeInertia

namespace Square

/-- The identity arrow on the image object satisfies the objectwise comparison equation. -/
private theorem comparisonIso.app_comm
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    ((viaTarget F).obj Z).aut.hom ≫ 𝟙 ((viaTarget F).obj Z).obj =
      𝟙 ((viaTarget F).obj Z).obj ≫ ((viaSource F).obj Z).aut.hom := sorry
/- Proof strategy: unfold the two routes and use `Z.mapAut_hom.symm`. -/

/-- Objectwise isomorphism comparing the two routes to inertia of the target. Its underlying
total-category isomorphism is the identity. -/
@[stacks 04Z6 "relative-inertia square comparison component"]
def comparisonIso.app
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    (viaTarget F).obj Z ≅ (viaSource F).obj Z :=
  CategoryTheory.RelativeInertia.isoMk Y.p (Iso.refl _)
    (comparisonIso.app_comm F Z)

/-- The objectwise inertia comparison is natural in relative-inertia morphisms.

This is the coherence equation used to assemble the based natural isomorphism; exposing it also
lets downstream constructions rewrite a route map without unfolding the comparison owner. -/
@[reassoc, stacks 04Z6 "relative-inertia square comparison naturality"]
theorem comparisonIso.naturality
    (F : X ⥤ᵇ Y) {Z Z' : CategoryTheory.RelativeInertia F.toFunctor} (f : Z ⟶ Z') :
    (viaTarget F).map f ≫ (comparisonIso.app F Z').hom =
      (comparisonIso.app F Z).hom ≫ (viaSource F).map f := sorry
/- Proof strategy: apply `RelativeInertia.hom_ext`; both underlying arrows reduce to the image
under `F` of the underlying arrow of `f`. -/

/-- The inverse objectwise comparison is natural in the opposite orientation.

This form is convenient when a downstream construction transports a morphism from the source
route back to the target route. -/
@[reassoc, stacks 04Z6 "relative-inertia square inverse comparison naturality"]
theorem comparisonIso.invNaturality
    (F : X ⥤ᵇ Y) {Z Z' : CategoryTheory.RelativeInertia F.toFunctor} (f : Z ⟶ Z') :
    (comparisonIso.app F Z).inv ≫ (viaTarget F).map f =
      (viaSource F).map f ≫ (comparisonIso.app F Z').inv := sorry

/-- Every forward objectwise comparison is vertical over the identity base map.

The named witness is part of the public based-category API, so callers constructing a further
based transformation can reuse it without unfolding `comparisonIso.app`. -/
@[stacks 04Z6 "relative-inertia square forward comparison hom-lift"]
theorem comparisonIso.app.hom.isHomLift
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    (inertia Y).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj Z))
      (comparisonIso.app F Z).hom := sorry
/- Proof strategy: unfold `comparisonIso.app`; its underlying arrow is the identity and the two
routes have the same base projection. -/

/-- The inverse objectwise comparison is vertical over the identity base map.

The witness is kept beside the forward one so objectwise users can work with the underlying
`Iso` without unpacking the packaged based natural isomorphism. -/
@[stacks 04Z6 "relative-inertia square inverse comparison hom-lift"]
theorem comparisonIso.app.inv.isHomLift
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    (inertia Y).p.IsHomLift
      (𝟙 ((relativeInertia F).p.obj Z))
      (comparisonIso.app F Z).inv := sorry

/-- Comparison between the target and source routes in `Cat/C`. -/
@[stacks 04Z6 "comparison in the relative-inertia square"]
def comparisonIso (F : X ⥤ᵇ Y) : viaTarget F ≅ viaSource F :=
  BasedNatIso.ofComponents
    (comparisonIso.app F)
    (fun f ↦ comparisonIso.naturality F f)
    (comparisonIso.app.hom.isHomLift F)

end Square

end RelativeInertia

end BasedCategory
end CategoryTheory
