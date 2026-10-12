/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Cat.Evaluation

/-!
# The canonical Cat-valued conical bilimit cone

The evaluation functors of `Bilimit.Cat.Evaluation` assemble into a strong transformation
from the constant diagram at the category of terminal-apex pseudocones. This file packages
that transformation as an explicit `PseudoCone`, proves its bilimit universal property, and
exposes the corresponding selected `BilimitCone` and existence instance.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe wJ vJ uJ vCat uCat

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.ConicalPseudoLimit

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

/-- Naturality with respect to `2`-morphisms for the universal evaluation cone. -/
private theorem πNaturalityNaturality (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    ∀ {a b : J} {f g : a ⟶ b} (η : f ⟶ g),
      (Pseudofunctor.const J (apex F)).map₂ η ▷ evaluation F b ≫
        (naturality F g).hom =
        (naturality F f).hom ≫
          evaluation F a ◁ (resizedDiagram F).map₂ η := sorry

/-- Identity coherence for the universal evaluation cone. -/
private theorem πNaturalityId (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    ∀ a : J,
      (naturality F (𝟙 a)).hom ≫
        evaluation F a ◁ ((resizedDiagram F).mapId a).hom =
        ((Pseudofunctor.const J (apex F)).mapId a).hom ▷
          evaluation F a ≫
          (λ_ (evaluation F a)).hom ≫
          (ρ_ (evaluation F a)).inv := sorry

/-- Composition coherence for the universal evaluation cone. -/
private theorem πNaturalityComp (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    ∀ {a b c : J} (f : a ⟶ b) (g : b ⟶ c),
      (naturality F (f ≫ g)).hom ≫
        evaluation F a ◁ ((resizedDiagram F).mapComp f g).hom =
        ((Pseudofunctor.const J (apex F)).mapComp f g).hom ▷
          evaluation F c ≫
          (α_ _ _ _).hom ≫
          (Pseudofunctor.const J (apex F)).map f ◁
            (naturality F g).hom ≫
          (α_ _ _ _).inv ≫
          (naturality F f).hom ▷ (resizedDiagram F).map g ≫
          (α_ _ _ _).hom := sorry

/-- The universal evaluation strong transformation from the constant diagram at the
category of terminal-apex pseudocones to the resized diagram. -/
noncomputable def π (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    Pseudofunctor.const J (apex F) ⟶ resizedDiagram F where
  app := evaluation F
  naturality := naturality F
  naturality_naturality := πNaturalityNaturality F
  naturality_id := πNaturalityId F
  naturality_comp := πNaturalityComp F

/-- The component of the universal evaluation transformation is the corresponding
evaluation functor. -/
@[simp]
theorem π_app (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J) :
    (π F).app j = evaluation F j := sorry

/-- The naturality isomorphism of the universal evaluation transformation is the
componentwise evaluation naturality. -/
@[simp]
theorem π_naturality (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) :
    (π F).naturality f = naturality F f := sorry

/-- The canonical conical pseudolimit cone of a Cat-valued pseudodiagram, after the
universe resizing needed to keep its apex and values in one ambient `Cat`. -/
noncomputable def cone (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    PseudoCone (resizedDiagram F) :=
  PseudoCone.mk (apex F) (π F)

/-- The apex of the canonical conical pseudolimit cone is its category of terminal-apex
pseudocones. -/
@[simp]
theorem cone_pt (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    (cone F).pt = apex F := sorry

/-- The strong transformation carried by the canonical conical pseudolimit cone is the
universal evaluation transformation. -/
@[simp]
theorem cone_π (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    (cone F).π = π F := sorry

/-- The component of the canonical conical pseudolimit cone at `j` is evaluation at `j`. -/
@[simp]
theorem cone_π_app (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J) :
    (cone F).π.app j = evaluation F j := sorry

/-- The naturality isomorphism of the canonical conical pseudolimit cone is the evaluation
naturality isomorphism. -/
@[simp]
theorem cone_π_naturality (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) :
    (cone F).π.naturality f = naturality F f := sorry

/-- The canonical evaluation cone represents conical pseudocones on the resized diagram. -/
instance coneIsBilimit (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    (cone F).IsBilimit := sorry

/-- The explicitly selected bilimit cone supplied by the Cat-valued conical pseudolimit
construction. -/
noncomputable def bilimitCone (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    BilimitCone (resizedDiagram F) :=
  BilimitCone.ofIsBilimit (cone F)

/-- The pseudocone stored by the selected Cat-valued bilimit cone is the canonical
evaluation cone. -/
@[simp]
theorem bilimitCone_cone (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    (bilimitCone F).cone = cone F := sorry

/-- The apex of the selected Cat-valued bilimit cone is the category of terminal-apex
pseudocones. -/
@[simp]
theorem bilimitCone_pt (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    (bilimitCone F).cone.pt = apex F := sorry

/-- The cone transformation of the selected Cat-valued bilimit cone is the universal evaluation
transformation. -/
@[simp]
theorem bilimitCone_π (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    (bilimitCone F).cone.π = π F := sorry

/-- The component of the selected Cat-valued bilimit cone at `j` is evaluation at `j`. -/
@[simp]
theorem bilimitCone_π_app (F : J ⥤ᵖ Cat.{vCat, uCat}) (j : J) :
    (bilimitCone F).cone.π.app j = evaluation F j := sorry

/-- The naturality isomorphism of the selected Cat-valued bilimit cone is the evaluation
naturality isomorphism. -/
@[simp]
theorem bilimitCone_π_naturality (F : J ⥤ᵖ Cat.{vCat, uCat})
    {a b : J} (f : a ⟶ b) :
    (bilimitCone F).cone.π.naturality f = naturality F f := sorry

/-- The resized Cat-valued pseudodiagram admits a conical bilimit. -/
instance hasBilimit (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    HasBilimit (resizedDiagram F) := sorry

/- Data and axiom audit (mathlib 4.32):

`π` stores the explicit evaluation functors and their componentwise naturality isomorphisms.
`cone` stores `apex F` and `π F`, while `bilimitCone` retains that same concrete cone together
with its `Prop`-valued universal property. Any `sorryAx` dependency is confined to the three
strong-transformation coherence fields, the bilimit proof, projection equalities, and inherited
categorical coherence. -/

end Bicategory.ConicalPseudoLimit

end CategoryTheory
