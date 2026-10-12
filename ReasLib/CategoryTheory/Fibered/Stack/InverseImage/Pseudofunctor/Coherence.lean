/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Pseudofunctor.Choice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherent global choices for inverse image

This file adds the identity, composition, and bicategorical coherence data required to promote a
global inverse-image choice to a pseudofunctor.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

set_option linter.checkUnivs false in
/-- A global inverse-image choice together with all comparison and coherence data needed for a
pseudofunctor.  The isomorphisms are explicit non-Prop data; only their coherence equations are
proof fields. -/
@[stacks 04WS "coherent inverse-image pseudofunctor choice"]
structure CoherentPseudofunctorChoice where
  /-- The underlying choices of inverse-image objects and Hom quasi-inverses. -/
  toChoice : PseudofunctorChoice (J := J) (K := K) u
  /-- The comparison between the selected image of an identity and the identity of the selected
  inverse-image object. -/
  mapId (S : StackOver.{uC, vC,
    max w₀ (max uC (max uD (max vC vD))),
    max w₁ (max w₀ (max uC (max uD (max vC vD))))} J) :
    toChoice.prelax.map (𝟙 S) ≅ 𝟙 (toChoice.prelax.obj S)
  /-- The comparison between the selected image of a composite and the composite of the selected
  images. -/
  mapComp {S T U : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
      (F : S ⟶ T) (G : T ⟶ U) :
    toChoice.prelax.map (F ≫ G) ≅
      toChoice.prelax.map F ≫ toChoice.prelax.map G
  /-- The chosen action on `2`-cells is compatible with left whiskering. -/
  map₂_whisker_left :
    ∀ {S T U : StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
      (F : S ⟶ T) {G H : T ⟶ U} (eta : G ⟶ H),
      toChoice.prelax.map₂ (F ◁ eta) =
        (mapComp F G).hom ≫
          toChoice.prelax.map F ◁ toChoice.prelax.map₂ eta ≫
            (mapComp F H).inv
  /-- The chosen action on `2`-cells is compatible with right whiskering. -/
  map₂_whisker_right :
    ∀ {S T U : StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
      {F G : S ⟶ T} (eta : F ⟶ G) (H : T ⟶ U),
      toChoice.prelax.map₂ (eta ▷ H) =
        (mapComp F H).hom ≫
          toChoice.prelax.map₂ eta ▷ toChoice.prelax.map H ≫
            (mapComp G H).inv
  /-- The selected composition comparisons satisfy associator coherence. -/
  map₂_associator :
    ∀ {R S T U : StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
      (F : R ⟶ S) (G : S ⟶ T) (H : T ⟶ U),
      toChoice.prelax.map₂ (α_ F G H).hom =
        (mapComp (F ≫ G) H).hom ≫
          (mapComp F G).hom ▷ toChoice.prelax.map H ≫
            (α_ (toChoice.prelax.map F) (toChoice.prelax.map G)
              (toChoice.prelax.map H)).hom ≫
              toChoice.prelax.map F ◁ (mapComp G H).inv ≫
                (mapComp F (G ≫ H)).inv
  /-- The selected identity and composition comparisons satisfy left-unitor coherence. -/
  map₂_left_unitor :
    ∀ {S T : StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J} (F : S ⟶ T),
      toChoice.prelax.map₂ (λ_ F).hom =
        (mapComp (𝟙 S) F).hom ≫
          (mapId S).hom ▷ toChoice.prelax.map F ≫
            (λ_ (toChoice.prelax.map F)).hom
  /-- The selected identity and composition comparisons satisfy right-unitor coherence. -/
  map₂_right_unitor :
    ∀ {S T : StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J} (F : S ⟶ T),
      toChoice.prelax.map₂ (ρ_ F).hom =
        (mapComp F (𝟙 T)).hom ≫
          toChoice.prelax.map F ◁ (mapId T).hom ≫
            (ρ_ (toChoice.prelax.map F)).hom

attribute [stacks 04WS "inverse-image underlying pseudofunctor choice"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.toChoice
attribute [stacks 04WS "inverse-image identity comparison choice"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.mapId
attribute [stacks 04WS "inverse-image composition comparison choice"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.mapComp
attribute [stacks 04WS "inverse-image left-whiskering coherence"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.map₂_whisker_left
attribute [stacks 04WS "inverse-image right-whiskering coherence"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.map₂_whisker_right
attribute [stacks 04WS "inverse-image associator coherence"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.map₂_associator
attribute [stacks 04WS "inverse-image left-unitor coherence"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.map₂_left_unitor
attribute [stacks 04WS "inverse-image right-unitor coherence"]
  StackOver.InverseImage.CoherentPseudofunctorChoice.map₂_right_unitor

-- Data audit: `mapId` and `mapComp` are supplied isomorphisms; the remaining fields are
-- Prop-valued bicategorical laws.

end StackOver.InverseImage

end CategoryTheory
