module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local coherence of pushforward

This leaf records identity, composition, and whiskering formulas for the chosen pushforward
actions. The pseudofunctor packaging is kept in a separate construction owner.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {X Y Z : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

set_option linter.checkUnivs false in
/-- 04WI: a coherent family of pushforward choices.  The objectwise projection and inversion proofs
are proposition-valued, while identity and composition comparisons are explicit isomorphisms. The
remaining fields are the five proposition-valued bicategorical coherence laws. -/
@[stacks 04WI "coherent pushforward pseudofunctor choice"]
structure CoherentInversionChoice
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] where
  /-- The projection choice for the pushforward of each object. -/
  obj (X : FiberedCategoryOver.{uC, vC, w₀, w₁} C) : ProjectionChoice u X
  /-- The inversion proof for every morphism of fibred categories. -/
  inverts {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (F : X ⟶ Y) :
    Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor F)
  /-- The explicit comparison for the image of an identity morphism. -/
  mapId (X : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    map u (𝟙 X) (obj X) (obj X) (inverts (𝟙 X)) ≅
      𝟙 (FiberedCategoryOver.pushforward u X (obj X))
  /-- The explicit comparison for the image of a composite morphism. -/
  mapComp {X Y Z : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
      (F : X ⟶ Y) (G : Y ⟶ Z) :
    map u (F ≫ G) (obj X) (obj Z) (inverts (F ≫ G)) ≅
      map u F (obj X) (obj Y) (inverts F) ≫
        map u G (obj Y) (obj Z) (inverts G)
  /-- Compatibility with left whiskering of `2`-cells. -/
  map₂_whisker_left :
    ∀ {X Y Z : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
      (F : X ⟶ Y) {G H : Y ⟶ Z} (eta : G ⟶ H),
      map₂ u (obj X) (obj Z) (inverts (F ≫ G)) (inverts (F ≫ H)) (F ◁ eta) =
        (mapComp F G).hom ≫
          map u F (obj X) (obj Y) (inverts F) ◁
            map₂ u (obj Y) (obj Z) (inverts G) (inverts H) eta ≫
              (mapComp F H).inv
  /-- Compatibility with right whiskering of `2`-cells. -/
  map₂_whisker_right :
    ∀ {X Y Z : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
      {F G : X ⟶ Y} (eta : F ⟶ G) (H : Y ⟶ Z),
      map₂ u (obj X) (obj Z) (inverts (F ≫ H)) (inverts (G ≫ H)) (eta ▷ H) =
        (mapComp F H).hom ≫
          map₂ u (obj X) (obj Y) (inverts F) (inverts G) eta ▷
            map u H (obj Y) (obj Z) (inverts H) ≫
              (mapComp G H).inv
  /-- Associator coherence for the selected pushforward action. -/
  map₂_associator :
    ∀ {W X Y Z : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
      (F : W ⟶ X) (G : X ⟶ Y) (H : Y ⟶ Z),
      map₂ u (obj W) (obj Z) (inverts ((F ≫ G) ≫ H))
          (inverts (F ≫ (G ≫ H))) (α_ F G H).hom =
        (mapComp (F ≫ G) H).hom ≫
          (mapComp F G).hom ▷ map u H (obj Y) (obj Z) (inverts H) ≫
            (α_ (map u F (obj W) (obj X) (inverts F))
              (map u G (obj X) (obj Y) (inverts G))
              (map u H (obj Y) (obj Z) (inverts H))).hom ≫
              map u F (obj W) (obj X) (inverts F) ◁ (mapComp G H).inv ≫
                (mapComp F (G ≫ H)).inv
  /-- Left-unitor coherence for the selected pushforward action. -/
  map₂_left_unitor :
    ∀ {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (F : X ⟶ Y),
      map₂ u (obj X) (obj Y) (inverts (𝟙 X ≫ F)) (inverts F) (λ_ F).hom =
        (mapComp (𝟙 X) F).hom ≫
          (mapId X).hom ▷ map u F (obj X) (obj Y) (inverts F) ≫
            (λ_ (map u F (obj X) (obj Y) (inverts F))).hom
  /-- Right-unitor coherence for the selected pushforward action. -/
  map₂_right_unitor :
    ∀ {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (F : X ⟶ Y),
      map₂ u (obj X) (obj Y) (inverts (F ≫ 𝟙 Y)) (inverts F) (ρ_ F).hom =
        (mapComp F (𝟙 Y)).hom ≫
          map u F (obj X) (obj Y) (inverts F) ◁ (mapId Y).hom ≫
            (ρ_ (map u F (obj X) (obj Y) (inverts F))).hom

attribute [stacks 04WI "coherent pushforward object choice field"]
  CoherentInversionChoice.obj
attribute [stacks 04WI "coherent pushforward inversion field"]
  CoherentInversionChoice.inverts
attribute [stacks 04WI "coherent pushforward identity comparison field"]
  CoherentInversionChoice.mapId
attribute [stacks 04WI "coherent pushforward composition comparison field"]
  CoherentInversionChoice.mapComp

section Hom

variable {u' : C ⥤ D}
variable [PreservesLimitsOfShape WalkingCospan u']
variable [PreservesLimitsOfShape WalkingParallelPair u']

set_option linter.defProp false in
/-- 04WI: restrict a coherent pushforward choice to one fixed Hom category by assembling its
existing endpoint choices and inversion family. -/
@[stacks 04WI "coherent pushforward Hom inversion choice"]
def CoherentInversionChoice.hom
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u')
    (X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C) : InversionChoice u' X Y :=
  { mapChoice := { inverts := fun F ↦ h.inverts F }
    source := h.obj X
    target := h.obj Y }

/-- The source endpoint of the Hom-level coherent choice is inherited from the global object
choice. -/
@[simp, stacks 04WI "coherent pushforward Hom source endpoint"]
theorem CoherentInversionChoice.hom.source
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u')
    (X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    (h.hom X Y).source = h.obj X := sorry

/-- The target endpoint of the Hom-level coherent choice is inherited from the global object
choice. -/
@[simp, stacks 04WI "coherent pushforward Hom target endpoint"]
theorem CoherentInversionChoice.hom.target
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u')
    (X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    (h.hom X Y).target = h.obj Y := sorry

/-- The inversion proof in a Hom-level coherent choice is inherited from the global choice. -/
@[simp, stacks 04WI "coherent pushforward Hom inversion readout"]
theorem CoherentInversionChoice.hom.inverts
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u')
    (X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C) (F : X ⟶ Y) :
    (h.hom X Y).inverts F = h.inverts F := sorry

end Hom

/-- The prelax core determined by the object and Hom-category actions of a coherent pushforward
choice.  The bicategorical comparison isomorphisms and coherence laws are added by
`pseudofunctor`; this owner exposes the reusable action layer on its own. -/
@[stacks 04WI "coherent pushforward prelax core"]
noncomputable def CoherentInversionChoice.prelax
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u) :
    PrelaxFunctor
      (FiberedCategoryOver.{uC, vC, w₀, w₁} C)
      (FiberedCategoryOver.{uD, vD,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} D) :=
  PrelaxFunctor.mkOfHomFunctors
    (fun X ↦ FiberedCategoryOver.pushforward u X (h.obj X))
    (fun X Y ↦ mapFunctor u (h.hom X Y))

namespace CoherentInversionChoice.prelax

/-- The coherent pushforward prelax core sends an object to its selected pushforward. -/
@[simp, stacks 04WI "coherent pushforward prelax object computation"]
theorem obj
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u)
    (X : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    h.prelax.obj X = FiberedCategoryOver.pushforward u X (h.obj X) := sorry

/-- The coherent pushforward prelax core uses the selected map on each `1`-cell. -/
@[simp, stacks 04WI "coherent pushforward prelax morphism computation"]
theorem map
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C} (F : X ⟶ Y) :
    h.prelax.map F = (mapFunctor u (h.hom X Y)).obj F := sorry

/-- The coherent pushforward prelax core uses the selected map on `2`-cells. -/
@[simp, stacks 04WI "coherent pushforward prelax two-cell computation"]
theorem map₂
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u)
    {X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    h.prelax.map₂ eta = (mapFunctor u (h.hom X Y)).map eta := sorry

/-- The Hom functor exposed by the coherent pushforward prelax core is the selected Hom functor. -/
@[simp, stacks 04WI "coherent pushforward prelax Hom computation"]
theorem mapFunctor
    (h : CoherentInversionChoice.{uC, uD, vC, vD, w₀, w₁} u)
    (X Y : FiberedCategoryOver.{uC, vC, w₀, w₁} C) :
    h.prelax.mapFunctor X Y = mapFunctor u (h.hom X Y) := sorry

end CoherentInversionChoice.prelax

-- Data audit: projection and inversion choices are Prop-valued fields, while `mapId` and `mapComp`
-- are explicit Iso data; only the five bicategorical coherence laws remain proof fields.

end FiberedCategoryOver.Pushforward

end CategoryTheory
