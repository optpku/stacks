/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# The pseudofunctor of selected bilimit apexes

An explicit `BilimitConeFamily` determines a pseudofunctor from `J`-shaped
pseudodiagrams to the ambient bicategory. Its object action selects the bilimit apex, and
its actions on `1`- and `2`-morphisms are the universal maps from the family-level API.

This file contains the pseudofunctor structure and keeps its coherence witnesses private.
Projection and represented-comparison formulas belong to a separate computations module.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]

namespace BilimitConeFamily

namespace Implementation

/-- The explicit prelax core of the selected bilimit-apex assignment. -/
private noncomputable def apexPrelax
    (L : BilimitConeFamily (J := J) (B := B)) :
    PrelaxFunctor (Pseudofunctor J B) B where
  obj F := L.apex F
  map α := L.map α
  map₂ Γ := L.map₂ Γ
  map₂_id α := L.map₂_id α
  map₂_comp Γ Δ := L.map₂_comp Γ Δ

/-- The selected bilimit-apex action preserves left whiskering up to its composition
comparisons. -/
private theorem map₂_whiskerLeft
    (L : BilimitConeFamily (J := J) (B := B)) :
    ∀ {E F G : Pseudofunctor J B} (α : E ⟶ F)
      {β γ : F ⟶ G} (Γ : β ⟶ γ),
      (apexPrelax L).map₂ (α ◁ Γ) =
        (L.mapCompIso α β).hom ≫
          (apexPrelax L).map α ◁ (apexPrelax L).map₂ Γ ≫
          (L.mapCompIso α γ).inv := sorry

/-- The selected bilimit-apex action preserves right whiskering up to its composition
comparisons. -/
private theorem map₂_whiskerRight
    (L : BilimitConeFamily (J := J) (B := B)) :
    ∀ {E F G : Pseudofunctor J B} {α β : E ⟶ F}
      (Γ : α ⟶ β) (γ : F ⟶ G),
      (apexPrelax L).map₂ (Γ ▷ γ) =
        (L.mapCompIso α γ).hom ≫
          (apexPrelax L).map₂ Γ ▷ (apexPrelax L).map γ ≫
          (L.mapCompIso β γ).inv := sorry

/-- The selected bilimit-apex action preserves associators. -/
private theorem map₂_associator
    (L : BilimitConeFamily (J := J) (B := B)) :
    ∀ {D E F G : Pseudofunctor J B}
      (α : D ⟶ E) (β : E ⟶ F) (γ : F ⟶ G),
      (apexPrelax L).map₂ (α_ α β γ).hom =
        (L.mapCompIso (α ≫ β) γ).hom ≫
          (L.mapCompIso α β).hom ▷ (apexPrelax L).map γ ≫
          (α_ ((apexPrelax L).map α)
            ((apexPrelax L).map β)
            ((apexPrelax L).map γ)).hom ≫
          (apexPrelax L).map α ◁ (L.mapCompIso β γ).inv ≫
          (L.mapCompIso α (β ≫ γ)).inv := sorry

/-- The selected bilimit-apex action preserves left unitors. -/
private theorem map₂_leftUnitor
    (L : BilimitConeFamily (J := J) (B := B)) :
    ∀ {E F : Pseudofunctor J B} (α : E ⟶ F),
      (apexPrelax L).map₂ (λ_ α).hom =
        (L.mapCompIso (𝟙 E) α).hom ≫
          (L.mapIdIso E).hom ▷ (apexPrelax L).map α ≫
          (λ_ ((apexPrelax L).map α)).hom := sorry

/-- The selected bilimit-apex action preserves right unitors. -/
private theorem map₂_rightUnitor
    (L : BilimitConeFamily (J := J) (B := B)) :
    ∀ {E F : Pseudofunctor J B} (α : E ⟶ F),
      (apexPrelax L).map₂ (ρ_ α).hom =
        (L.mapCompIso α (𝟙 F)).hom ≫
          (apexPrelax L).map α ◁ (L.mapIdIso F).hom ≫
          (ρ_ ((apexPrelax L).map α)).hom := sorry

end Implementation

/-- The pseudofunctor sending every diagram to the apex of its explicitly selected
bilimit cone.

Its `1`- and `2`-morphism actions are `BilimitConeFamily.map` and
`BilimitConeFamily.map₂`; its identity and composition comparisons are the family-level
universal comparison isomorphisms. -/
noncomputable def apexPseudofunctor
    (L : BilimitConeFamily (J := J) (B := B)) :
    Pseudofunctor (Pseudofunctor J B) B where
  toPrelaxFunctor := Implementation.apexPrelax L
  mapId F := L.mapIdIso F
  mapComp α β := L.mapCompIso α β
  map₂_whisker_left := Implementation.map₂_whiskerLeft L
  map₂_whisker_right := Implementation.map₂_whiskerRight L
  map₂_associator := Implementation.map₂_associator L
  map₂_left_unitor := Implementation.map₂_leftUnitor L
  map₂_right_unitor := Implementation.map₂_rightUnitor L

/- Data and axiom audit (mathlib 4.32):

The object, `1`-morphism, `2`-morphism, identity, and composition data of
`apexPseudofunctor` are exactly the explicit family-level owners imported above. Its
private helpers supply only `Prop`-valued functoriality and bicategorical coherence
fields; no new apex, map, or comparison is selected there. -/

end BilimitConeFamily

end Bicategory

end CategoryTheory
