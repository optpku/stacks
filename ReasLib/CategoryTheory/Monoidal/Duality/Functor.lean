module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong monoidal functors preserve exact pairings

The coevaluation and evaluation of the image pairing are explicit composites of the unit and
tensor comparison isomorphisms of the functor.  Only the two triangle identities are deferred.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactPairing

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The coevaluation obtained by applying a strong monoidal functor to an explicit exact
pairing. -/
def mapCoevaluation {X Y : C} (p : ExactPairing X Y) (F : C ⥤ D) [F.Monoidal] :
    𝟙_ D ⟶ F.obj X ⊗ F.obj Y :=
  (Functor.Monoidal.εIso F).hom ≫ F.map p.coevaluation' ≫
    (Functor.Monoidal.μIso F X Y).inv

/-- The evaluation obtained by applying a strong monoidal functor to an explicit exact
pairing. -/
def mapEvaluation {X Y : C} (p : ExactPairing X Y) (F : C ⥤ D) [F.Monoidal] :
    F.obj Y ⊗ F.obj X ⟶ 𝟙_ D :=
  (Functor.Monoidal.μIso F Y X).hom ≫ F.map p.evaluation' ≫
    (Functor.Monoidal.εIso F).inv

/-- The image coevaluation and evaluation satisfy the triangle identity on the second object. -/
theorem map_coevaluation_evaluation
    {X Y : C} (p : ExactPairing X Y) (F : C ⥤ D) [F.Monoidal] :
    F.obj Y ◁ p.mapCoevaluation F ≫
        (α_ (F.obj Y) (F.obj X) (F.obj Y)).inv ≫
        p.mapEvaluation F ▷ F.obj Y =
      (ρ_ (F.obj Y)).hom ≫ (λ_ (F.obj Y)).inv := by
  calc
    _ = F.obj Y ◁ (Functor.Monoidal.εIso F).hom ≫
        (Functor.Monoidal.μIso F Y (𝟙_ C)).hom ≫
        F.map (Y ◁ p.coevaluation' ≫ (α_ Y X Y).inv ≫
          p.evaluation' ▷ Y) ≫
        (Functor.Monoidal.μIso F (𝟙_ C) Y).inv ≫
        (Functor.Monoidal.εIso F).inv ▷ F.obj Y := by
      dsimp [mapCoevaluation, mapEvaluation]
      simp only [MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.comp_whiskerRight, Category.assoc]
      rw [cancel_epi (F.obj Y ◁ (Functor.Monoidal.εIso F).hom)]
      simp only [← Category.assoc]
      rw [cancel_mono ((Functor.Monoidal.εIso F).inv ▷ F.obj Y)]
      simp only [Category.assoc]
      rw [← cancel_epi (Functor.Monoidal.μIso F Y (𝟙_ C)).inv]
      rw [← cancel_mono (Functor.Monoidal.μIso F (𝟙_ C) Y).hom]
      simp only [Iso.inv_hom_id_assoc]
      rw [F.map_comp, F.map_comp,
        Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_associator_inv,
        Functor.Monoidal.map_whiskerRight]
      simp only [Functor.Monoidal.μIso_inv,
        Functor.Monoidal.μIso_hom, Category.assoc,
        Functor.Monoidal.μ_δ_assoc]
    _ = F.obj Y ◁ (Functor.Monoidal.εIso F).hom ≫
        (Functor.Monoidal.μIso F Y (𝟙_ C)).hom ≫
        F.map ((ρ_ Y).hom ≫ (λ_ Y).inv) ≫
        (Functor.Monoidal.μIso F (𝟙_ C) Y).inv ≫
        (Functor.Monoidal.εIso F).inv ▷ F.obj Y := by
      rw [p.coevaluation_evaluation']
    _ = _ := by
      rw [F.map_comp, Functor.Monoidal.map_rightUnitor,
        Functor.Monoidal.map_leftUnitor_inv]
      simp

/-- The image coevaluation and evaluation satisfy the triangle identity on the first object. -/
theorem map_evaluation_coevaluation
    {X Y : C} (p : ExactPairing X Y) (F : C ⥤ D) [F.Monoidal] :
    p.mapCoevaluation F ▷ F.obj X ≫
        (α_ (F.obj X) (F.obj Y) (F.obj X)).hom ≫
        F.obj X ◁ p.mapEvaluation F =
      (λ_ (F.obj X)).hom ≫ (ρ_ (F.obj X)).inv := by
  calc
    _ = (Functor.Monoidal.εIso F).hom ▷ F.obj X ≫
        (Functor.Monoidal.μIso F (𝟙_ C) X).hom ≫
        F.map (p.coevaluation' ▷ X ≫ (α_ X Y X).hom ≫
          X ◁ p.evaluation') ≫
        (Functor.Monoidal.μIso F X (𝟙_ C)).inv ≫
        F.obj X ◁ (Functor.Monoidal.εIso F).inv := by
      dsimp [mapCoevaluation, mapEvaluation]
      simp only [MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.comp_whiskerRight, Category.assoc]
      rw [cancel_epi ((Functor.Monoidal.εIso F).hom ▷ F.obj X)]
      simp only [← Category.assoc]
      rw [cancel_mono (F.obj X ◁ (Functor.Monoidal.εIso F).inv)]
      simp only [Category.assoc]
      rw [← cancel_epi (Functor.Monoidal.μIso F (𝟙_ C) X).inv]
      rw [← cancel_mono (Functor.Monoidal.μIso F X (𝟙_ C)).hom]
      simp only [Iso.inv_hom_id_assoc]
      rw [F.map_comp, F.map_comp,
        Functor.Monoidal.map_whiskerRight,
        Functor.Monoidal.map_associator,
        Functor.Monoidal.map_whiskerLeft]
      simp only [Functor.Monoidal.μIso_inv,
        Functor.Monoidal.μIso_hom, Category.assoc,
        Functor.Monoidal.μ_δ_assoc]
    _ = (Functor.Monoidal.εIso F).hom ▷ F.obj X ≫
        (Functor.Monoidal.μIso F (𝟙_ C) X).hom ≫
        F.map ((λ_ X).hom ≫ (ρ_ X).inv) ≫
        (Functor.Monoidal.μIso F X (𝟙_ C)).inv ≫
        F.obj X ◁ (Functor.Monoidal.εIso F).inv := by
      rw [p.evaluation_coevaluation']
    _ = _ := by
      rw [F.map_comp, Functor.Monoidal.map_leftUnitor,
        Functor.Monoidal.map_rightUnitor_inv]
      simp

/-- A strong monoidal functor sends explicit exact-pairing data to explicit exact-pairing data. -/
@[stacks 0E8I "strong monoidal image of an exact pairing", implicit_reducible]
def map {X Y : C} (p : ExactPairing X Y) (F : C ⥤ D) [F.Monoidal] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := p.mapCoevaluation F
  evaluation' := p.mapEvaluation F
  coevaluation_evaluation' := p.map_coevaluation_evaluation F
  evaluation_coevaluation' := p.map_evaluation_coevaluation F



end CategoryTheory.ExactPairing
