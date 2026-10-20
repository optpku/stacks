module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Construction
public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Precompose.Naturality.Source
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell
import Mathlib.Tactic.CrossRefAttribute

/-!
# Source naturality of the pushforward-pullback Hom functor

This leaf records compatibility between pushforward on a source morphism and the Hom comparison.
The resulting natural isomorphism packages the full three-step composite used by inverse-image
constructions.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

namespace Hom

/-- Applying the Hom comparison after pushing a source morphism forward and postcomposing agrees
with postcomposition of the original source morphism after the Hom comparison. -/
@[stacks 04WI "bundled Hom source naturality"]
theorem obj.mapPostcomp
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (F : X ⟶ Y) (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z) :
    obj u (FiberedCategoryOver.Pushforward.map u F h.source h.target (h.inverts F) ≫ G) =
      F ≫ obj u G := sorry

/-- The explicit source-variable comparison for the pushforward-pullback Hom construction. Its
underlying based-functor data are the neutral comparison from `Precompose.Source.iso`; no
equality proof is converted into morphism data. -/
@[stacks 04WI "bundled Hom source comparison isomorphism"]
noncomputable def mapPostcompIso
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (F : X ⟶ Y) (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z) :
    obj u (FiberedCategoryOver.Pushforward.map u F h.source h.target (h.inverts F) ≫ G) ≅
      F ≫ obj u G :=
  FiberedCategoryOver.BasedFunctorIso.lift
    (Precompose.Source.iso u h.source h.target
      (FiberedCategoryOver.toCartesianBasedFunctor F) (h.inverts F)
      (FiberedCategoryOver.toBasedFunctor G))

/-- The total-category component of the forward bundled source comparison is the explicit lower
pullback comparison. -/
@[simp, stacks 04WI "bundled Hom source comparison forward component"]
theorem mapPostcompIso.hom.app
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (F : X ⟶ Y) (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z)
    (x : X.total) :
    (FiberedCategoryOver.toNatTrans (mapPostcompIso u h F G).hom).app x =
      (Precompose.Source.app u h.source h.target
        (FiberedCategoryOver.toCartesianBasedFunctor F) (h.inverts F)
        (FiberedCategoryOver.toBasedFunctor G) x).hom := sorry

/-- The total-category component of the inverse bundled source comparison is the inverse
explicit lower pullback comparison. -/
@[simp, stacks 04WI "bundled Hom source comparison inverse component"]
theorem mapPostcompIso.inv.app
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (F : X ⟶ Y) (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z)
    (x : X.total) :
    (FiberedCategoryOver.toNatTrans (mapPostcompIso u h F G).inv).app x =
      (Precompose.Source.app u h.source h.target
        (FiberedCategoryOver.toCartesianBasedFunctor F) (h.inverts F)
        (FiberedCategoryOver.toBasedFunctor G) x).inv := sorry

/-- The bundled source-comparison components are natural in vertical transformations of the
source morphism. -/
@[stacks 04WI "bundled Hom source comparison naturality"]
theorem map.mapPostcomp
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    {F F' : X ⟶ Y} (eta : F ⟶ F')
    (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z) :
    map u (FiberedCategoryOver.Pushforward.map₂ u h.source h.target
        (h.inverts F) (h.inverts F') eta ▷ G) ≫
        (mapPostcompIso u h F' G).hom =
      (mapPostcompIso u h F G).hom ≫ eta ▷ obj u G := sorry

end Hom

namespace homFunctor

/-- Source-variable naturality of the pushforward-pullback Hom functor. Pushing a morphism,
postcomposing, and applying the Hom comparison agrees canonically with postcomposition after the
Hom comparison. -/
@[stacks 04WI "Hom functor source naturality isomorphism"]
noncomputable def mapPostcompIso
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z) :
    FiberedCategoryOver.Pushforward.mapFunctor u h ⋙
        Bicategory.postcomp (FiberedCategoryOver.pushforward u X h.source) G ⋙
          homFunctor u h.source Z ≅
      Bicategory.postcomp X (Hom.obj u G) :=
  NatIso.ofComponents (fun F ↦ Hom.mapPostcompIso u h F G)
    (fun eta ↦ Hom.map.mapPostcomp u h eta G)

/-- The forward component of bundled source naturality is the explicit source comparison. -/
@[simp, stacks 04WI "Hom functor source naturality forward component"]
theorem mapPostcompIso.hom.app
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z) (F : X ⟶ Y) :
    (mapPostcompIso u h G).hom.app F = (Hom.mapPostcompIso u h F G).hom := sorry

/-- The inverse component of bundled source naturality is the inverse explicit source
comparison. -/
@[simp, stacks 04WI "Hom functor source naturality inverse component"]
theorem mapPostcompIso.inv.app
    {X Y : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    (h : InversionChoice u X Y)
    {Z : FiberedCategoryOver.{uD, vD,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} D}
    (G : FiberedCategoryOver.pushforward u Y h.target ⟶ Z) (F : X ⟶ Y) :
    (mapPostcompIso u h G).inv.app F = (Hom.mapPostcompIso u h F G).inv := sorry

end homFunctor

/- Axiom audit: every non-Prop component of `Hom.mapPostcompIso` is inherited from the explicit
lower `Precompose.Source.iso`; the remaining `sorryAx` dependencies are confined to compatibility,
naturality, verticality, inverse laws, and proof fields of the bundled owners. -/

end FiberedCategoryOver.Pushforward

end CategoryTheory
