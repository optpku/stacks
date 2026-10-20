module

public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

/-!
# Horizontal composition of adjunction base-change maps

Mathlib proves that `mateEquiv` preserves horizontal composition of squares. This file exposes the
corresponding objectwise API: the pasted square, the composite of two chosen mate components, and
the canonical-mate comparison. It is independent of derived categories and ringed geometry.
-/

open CategoryTheory
open scoped CategoryTheory.TwoSquare

noncomputable section

universe uX₀ uX₁ uX₂ uY₀ uY₁ uY₂ vX₀ vX₁ vX₂ vY₀ vY₁ vY₂

namespace CategoryTheory.DerivedBaseChange.HorizontalComposition

section

variable {X₀ : Type uX₀} {X₁ : Type uX₁} {X₂ : Type uX₂}
variable {Y₀ : Type uY₀} {Y₁ : Type uY₁} {Y₂ : Type uY₂}
variable [Category.{vX₀} X₀] [Category.{vX₁} X₁] [Category.{vX₂} X₂]
variable [Category.{vY₀} Y₀] [Category.{vY₁} Y₁] [Category.{vY₂} Y₂]
variable (L₀ : Y₀ ⥤ X₀) (L₁ : Y₁ ⥤ X₁) (L₂ : Y₂ ⥤ X₂)
variable (R₀ : X₀ ⥤ Y₀) (R₁ : X₁ ⥤ Y₁) (R₂ : X₂ ⥤ Y₂)
variable (U₀ : Y₀ ⥤ Y₁) (U₁ : Y₁ ⥤ Y₂) (U : Y₀ ⥤ Y₂)
variable (V₀ : X₀ ⥤ X₁) (V₁ : X₁ ⥤ X₂) (V : X₀ ⥤ X₂)
variable (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The outer square obtained by horizontally pasting two functor squares and transporting both
vertical composites along specified comparison isomorphisms. -/
@[stacks 0E47 "explicitly assembled horizontally pasted adjunction square"]
noncomputable abbrev squareIsoExplicit
    (square₀ : U₀ ⋙ L₁ ≅ L₀ ⋙ V₀)
    (square₁ : U₁ ⋙ L₂ ≅ L₁ ⋙ V₁)
    (leftComp : U ≅ U₀ ⋙ U₁)
    (rightComp : V ≅ V₀ ⋙ V₁) :
    U ⋙ L₂ ≅ L₀ ⋙ V :=
  Functor.isoWhiskerRight leftComp L₂ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft U₀ square₁ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight square₀ V₁ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft L₀ rightComp.symm

/-- The outer square obtained by horizontally pasting two functor squares.  The functors are
inferred from the square and comparison isomorphisms; only the mathematical comparison data are
explicit. -/
@[stacks 0E47 "horizontally pasted adjunction square"]
noncomputable abbrev squareIso
    {L₀ : Y₀ ⥤ X₀} {L₁ : Y₁ ⥤ X₁} {L₂ : Y₂ ⥤ X₂}
    {U₀ : Y₀ ⥤ Y₁} {U₁ : Y₁ ⥤ Y₂} {U : Y₀ ⥤ Y₂}
    {V₀ : X₀ ⥤ X₁} {V₁ : X₁ ⥤ X₂} {V : X₀ ⥤ X₂}
    (square₀ : U₀ ⋙ L₁ ≅ L₀ ⋙ V₀)
    (square₁ : U₁ ⋙ L₂ ≅ L₁ ⋙ V₁)
    (leftComp : U ≅ U₀ ⋙ U₁)
    (rightComp : V ≅ V₀ ⋙ V₁) :
    U ⋙ L₂ ≅ L₀ ⋙ V :=
  squareIsoExplicit L₀ L₁ L₂ U₀ U₁ U V₀ V₁ V square₀ square₁ leftComp rightComp

/-- The objectwise horizontal composite of two chosen base-change morphisms, transported from
the iterated vertical functors to their specified composites. -/
@[stacks 0E47 "explicit horizontal composite of adjunction base-change components"]
noncomputable def mapExplicit
    (leftComp : U ≅ U₀ ⋙ U₁)
    (rightComp : V ≅ V₀ ⋙ V₁)
    (K : X₀)
    (η₀ : U₀.obj (R₀.obj K) ⟶ R₁.obj (V₀.obj K))
    (η₁ : U₁.obj (R₁.obj (V₀.obj K)) ⟶ R₂.obj (V₁.obj (V₀.obj K))) :
    U.obj (R₀.obj K) ⟶ R₂.obj (V.obj K) :=
  leftComp.hom.app (R₀.obj K) ≫ U₁.map η₀ ≫ η₁ ≫ R₂.map (rightComp.inv.app K)

/-- The objectwise horizontal composite of two base-change morphisms.  Functors are inferred from
the comparison data and the two components. -/
@[stacks 0E47 "horizontal composite of adjunction base-change components"]
noncomputable abbrev map
    {R₀ : X₀ ⥤ Y₀} {R₁ : X₁ ⥤ Y₁} {R₂ : X₂ ⥤ Y₂}
    {U₀ : Y₀ ⥤ Y₁} {U₁ : Y₁ ⥤ Y₂} {U : Y₀ ⥤ Y₂}
    {V₀ : X₀ ⥤ X₁} {V₁ : X₁ ⥤ X₂} {V : X₀ ⥤ X₂}
    (leftComp : U ≅ U₀ ⋙ U₁)
    (rightComp : V ≅ V₀ ⋙ V₁)
    (K : X₀)
    (η₀ : U₀.obj (R₀.obj K) ⟶ R₁.obj (V₀.obj K))
    (η₁ : U₁.obj (R₁.obj (V₀.obj K)) ⟶ R₂.obj (V₁.obj (V₀.obj K))) :
    U.obj (R₀.obj K) ⟶ R₂.obj (V.obj K) :=
  mapExplicit R₀ R₁ R₂ U₀ U₁ U V₀ V₁ V leftComp rightComp K η₀ η₁

/-- Horizontal composition preserves the objectwise adjunction-transpose characterization of
base-change morphisms. -/
@[stacks 0E47 "horizontal composition preserves adjunction mates"]
theorem map_isMapExplicit
    (square₀ : U₀ ⋙ L₁ ≅ L₀ ⋙ V₀)
    (square₁ : U₁ ⋙ L₂ ≅ L₁ ⋙ V₁)
    (leftComp : U ≅ U₀ ⋙ U₁)
    (rightComp : V ≅ V₀ ⋙ V₁)
    (K : X₀)
    (η₀ : U₀.obj (R₀.obj K) ⟶ R₁.obj (V₀.obj K))
    (η₁ : U₁.obj (R₁.obj (V₀.obj K)) ⟶ R₂.obj (V₁.obj (V₀.obj K)))
    (h₀ : IsDerivedBaseChangeMap L₀ L₁ U₀ V₀ R₀ R₁ adj₀ adj₁ square₀ K η₀)
    (h₁ : IsDerivedBaseChangeMap L₁ L₂ U₁ V₁ R₁ R₂ adj₁ adj₂ square₁
      (V₀.obj K) η₁) :
    IsDerivedBaseChangeMap L₀ L₂ U V R₀ R₂ adj₀ adj₂
      (squareIsoExplicit L₀ L₁ L₂ U₀ U₁ U V₀ V₁ V square₀ square₁ leftComp rightComp) K
      (mapExplicit R₀ R₁ R₂ U₀ U₁ U V₀ V₁ V leftComp rightComp K η₀ η₁) := sorry

/-- Horizontal composition preserves the objectwise adjunction-transpose characterization of
base-change morphisms. -/
@[stacks 0E47 "horizontal composition preserves adjunction mates"]
theorem map_isMap
    {L₀ : Y₀ ⥤ X₀} {L₁ : Y₁ ⥤ X₁} {L₂ : Y₂ ⥤ X₂}
    {R₀ : X₀ ⥤ Y₀} {R₁ : X₁ ⥤ Y₁} {R₂ : X₂ ⥤ Y₂}
    {U₀ : Y₀ ⥤ Y₁} {U₁ : Y₁ ⥤ Y₂} {U : Y₀ ⥤ Y₂}
    {V₀ : X₀ ⥤ X₁} {V₁ : X₁ ⥤ X₂} {V : X₀ ⥤ X₂}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (square₀ : U₀ ⋙ L₁ ≅ L₀ ⋙ V₀)
    (square₁ : U₁ ⋙ L₂ ≅ L₁ ⋙ V₁)
    (leftComp : U ≅ U₀ ⋙ U₁) (rightComp : V ≅ V₀ ⋙ V₁)
    (K : X₀)
    (η₀ : U₀.obj (R₀.obj K) ⟶ R₁.obj (V₀.obj K))
    (η₁ : U₁.obj (R₁.obj (V₀.obj K)) ⟶ R₂.obj (V₁.obj (V₀.obj K)))
    (h₀ : IsDerivedBaseChangeMap L₀ L₁ U₀ V₀ R₀ R₁ adj₀ adj₁ square₀ K η₀)
    (h₁ : IsDerivedBaseChangeMap L₁ L₂ U₁ V₁ R₁ R₂ adj₁ adj₂ square₁
      (V₀.obj K) η₁) :
    IsDerivedBaseChangeMap L₀ L₂ U V R₀ R₂ adj₀ adj₂
      (squareIso square₀ square₁ leftComp rightComp) K
      (map leftComp rightComp K η₀ η₁) := sorry

/-- The horizontal composite of two canonical objectwise mates is the canonical mate of the
pasted square. -/
@[stacks 0E47 "canonical adjunction base-change maps compose horizontally"]
theorem map_eqExplicit
    (square₀ : U₀ ⋙ L₁ ≅ L₀ ⋙ V₀)
    (square₁ : U₁ ⋙ L₂ ≅ L₁ ⋙ V₁)
    (leftComp : U ≅ U₀ ⋙ U₁)
    (rightComp : V ≅ V₀ ⋙ V₁)
    (K : X₀) :
    mapExplicit R₀ R₁ R₂ U₀ U₁ U V₀ V₁ V leftComp rightComp K
        (derivedBaseChangeMap L₀ L₁ U₀ V₀ R₀ R₁ adj₀ adj₁ square₀ K)
        (derivedBaseChangeMap L₁ L₂ U₁ V₁ R₁ R₂ adj₁ adj₂ square₁ (V₀.obj K)) =
      derivedBaseChangeMap L₀ L₂ U V R₀ R₂ adj₀ adj₂
        (squareIsoExplicit L₀ L₁ L₂ U₀ U₁ U V₀ V₁ V square₀ square₁ leftComp rightComp) K := sorry

/-- The horizontal composite of two canonical objectwise mates is the canonical mate of the
pasted square. -/
@[stacks 0E47 "canonical adjunction base-change maps compose horizontally"]
theorem map_eq
    {L₀ : Y₀ ⥤ X₀} {L₁ : Y₁ ⥤ X₁} {L₂ : Y₂ ⥤ X₂}
    {R₀ : X₀ ⥤ Y₀} {R₁ : X₁ ⥤ Y₁} {R₂ : X₂ ⥤ Y₂}
    {U₀ : Y₀ ⥤ Y₁} {U₁ : Y₁ ⥤ Y₂} {U : Y₀ ⥤ Y₂}
    {V₀ : X₀ ⥤ X₁} {V₁ : X₁ ⥤ X₂} {V : X₀ ⥤ X₂}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (square₀ : U₀ ⋙ L₁ ≅ L₀ ⋙ V₀)
    (square₁ : U₁ ⋙ L₂ ≅ L₁ ⋙ V₁)
    (leftComp : U ≅ U₀ ⋙ U₁) (rightComp : V ≅ V₀ ⋙ V₁)
    (K : X₀) :
    map leftComp rightComp K
        (derivedBaseChangeMap L₀ L₁ U₀ V₀ R₀ R₁ adj₀ adj₁ square₀ K)
        (derivedBaseChangeMap L₁ L₂ U₁ V₁ R₁ R₂ adj₁ adj₂ square₁ (V₀.obj K)) =
      derivedBaseChangeMap L₀ L₂ U V R₀ R₂ adj₀ adj₂
        (squareIso square₀ square₁ leftComp rightComp) K := sorry

end

end CategoryTheory.DerivedBaseChange.HorizontalComposition

namespace CategoryTheory.DerivedBaseChange

universe uA uB uC uD uE uF vA vB vC vD vE vF

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}

/-- Taking inverse mates sends horizontal composition of right-adjoint squares to vertical
composition of the corresponding left-adjoint squares. -/
public theorem mapOfRight_hcomp
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (alpha : TwoSquare R₁ H G R₂) (beta : TwoSquare R₃ K H R₄) :
    mapOfRight (adj₁.comp adj₃) (adj₂.comp adj₄) (beta ≫ₕ alpha) =
      mapOfRight adj₁ adj₂ alpha ≫ᵥ mapOfRight adj₃ adj₄ beta := sorry

end CategoryTheory.DerivedBaseChange
