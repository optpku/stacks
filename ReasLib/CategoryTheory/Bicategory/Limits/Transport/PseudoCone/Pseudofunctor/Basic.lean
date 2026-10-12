/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Functoriality.Identity

/-!
# The pseudofunctor transporting conical pseudocones

This module assembles the data-level action and its identity and composition comparisons into
a pseudofunctor on arbitrary conical pseudocones. Projection-level computation lemmas are kept
in a separate downstream module.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

namespace Implementation

/-- Mapping pseudocone `2`-morphisms preserves identities. -/
private theorem mapPseudoCone.pseudofunctor.map₂.id {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    mapPseudoCone.map₂ K (𝟙 u) = 𝟙 (mapPseudoCone.map K u) := sorry

/-- Mapping pseudocone `2`-morphisms preserves vertical composition. -/
private theorem mapPseudoCone.pseudofunctor.map₂.comp {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E}
    {u v w : S ⟶ T} (η : u ⟶ v) (θ : v ⟶ w) :
    mapPseudoCone.map₂ K (η ≫ θ) =
      mapPseudoCone.map₂ K η ≫ mapPseudoCone.map₂ K θ := sorry

/-- The explicit prelax core for transport of conical pseudocones. -/
private def mapPseudoCone.pseudofunctor.prelax (K : Pseudofunctor B D)
    (E : Pseudofunctor J B) :
    PrelaxFunctor (Bicategory.PseudoCone E)
      (Bicategory.PseudoCone (E.comp K)) where
  obj := mapPseudoCone K
  map := mapPseudoCone.map K
  map₂ := mapPseudoCone.map₂ K
  map₂_id := mapPseudoCone.pseudofunctor.map₂.id K
  map₂_comp := mapPseudoCone.pseudofunctor.map₂.comp K

/-- Transport of pseudocones preserves left whiskering up to its explicit composition
comparisons. -/
private theorem mapPseudoCone.pseudofunctor.map₂.whiskerLeft {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) :
    ∀ {S T U : Bicategory.PseudoCone E} (u : S ⟶ T)
      {v w : T ⟶ U} (η : v ⟶ w),
      (mapPseudoCone.pseudofunctor.prelax K E).map₂ (u ◁ η) =
        (mapPseudoCone.mapComp K u v).hom ≫
          (mapPseudoCone.pseudofunctor.prelax K E).map u ◁
            (mapPseudoCone.pseudofunctor.prelax K E).map₂ η ≫
          (mapPseudoCone.mapComp K u w).inv := sorry

/-- Transport of pseudocones preserves right whiskering up to its explicit composition
comparisons. -/
private theorem mapPseudoCone.pseudofunctor.map₂.whiskerRight {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) :
    ∀ {S T U : Bicategory.PseudoCone E} {u v : S ⟶ T}
      (η : u ⟶ v) (w : T ⟶ U),
      (mapPseudoCone.pseudofunctor.prelax K E).map₂ (η ▷ w) =
        (mapPseudoCone.mapComp K u w).hom ≫
          (mapPseudoCone.pseudofunctor.prelax K E).map₂ η ▷
            (mapPseudoCone.pseudofunctor.prelax K E).map w ≫
          (mapPseudoCone.mapComp K v w).inv := sorry

/-- Transport of pseudocones preserves associators. -/
private theorem mapPseudoCone.pseudofunctor.map₂.associator {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) :
    ∀ {R S T U : Bicategory.PseudoCone E}
      (u : R ⟶ S) (v : S ⟶ T) (w : T ⟶ U),
      (mapPseudoCone.pseudofunctor.prelax K E).map₂ (α_ u v w).hom =
        (mapPseudoCone.mapComp K (u ≫ v) w).hom ≫
          (mapPseudoCone.mapComp K u v).hom ▷
            (mapPseudoCone.pseudofunctor.prelax K E).map w ≫
          (α_ ((mapPseudoCone.pseudofunctor.prelax K E).map u)
            ((mapPseudoCone.pseudofunctor.prelax K E).map v)
            ((mapPseudoCone.pseudofunctor.prelax K E).map w)).hom ≫
          (mapPseudoCone.pseudofunctor.prelax K E).map u ◁
            (mapPseudoCone.mapComp K v w).inv ≫
          (mapPseudoCone.mapComp K u (v ≫ w)).inv := sorry

/-- Transport of pseudocones preserves left unitors. -/
private theorem mapPseudoCone.pseudofunctor.map₂.leftUnitor {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) :
    ∀ {S T : Bicategory.PseudoCone E} (u : S ⟶ T),
      (mapPseudoCone.pseudofunctor.prelax K E).map₂ (λ_ u).hom =
        (mapPseudoCone.mapComp K (𝟙 S) u).hom ≫
          (mapPseudoCone.mapId K S).hom ▷
            (mapPseudoCone.pseudofunctor.prelax K E).map u ≫
          (λ_ ((mapPseudoCone.pseudofunctor.prelax K E).map u)).hom := sorry

/-- Transport of pseudocones preserves right unitors. -/
private theorem mapPseudoCone.pseudofunctor.map₂.rightUnitor {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) :
    ∀ {S T : Bicategory.PseudoCone E} (u : S ⟶ T),
      (mapPseudoCone.pseudofunctor.prelax K E).map₂ (ρ_ u).hom =
        (mapPseudoCone.mapComp K u (𝟙 T)).hom ≫
          (mapPseudoCone.pseudofunctor.prelax K E).map u ◁
            (mapPseudoCone.mapId K T).hom ≫
          (ρ_ ((mapPseudoCone.pseudofunctor.prelax K E).map u)).hom := sorry

end Implementation

/-- Mapping conical pseudocones along `K` is a pseudofunctor.

Its object, `1`-morphism, and `2`-morphism actions are `mapPseudoCone`,
`mapPseudoCone.map`, and `mapPseudoCone.map₂`. Its identity and composition comparisons
are inherited pointwise from those of `K`. -/
def mapPseudoCone.pseudofunctor (K : Pseudofunctor B D)
    (E : Pseudofunctor J B) :
    Pseudofunctor (Bicategory.PseudoCone E)
      (Bicategory.PseudoCone (E.comp K)) where
  toPrelaxFunctor := Implementation.mapPseudoCone.pseudofunctor.prelax K E
  mapId := mapPseudoCone.mapId K
  mapComp := mapPseudoCone.mapComp K
  map₂_whisker_left := Implementation.mapPseudoCone.pseudofunctor.map₂.whiskerLeft K
  map₂_whisker_right := Implementation.mapPseudoCone.pseudofunctor.map₂.whiskerRight K
  map₂_associator := Implementation.mapPseudoCone.pseudofunctor.map₂.associator K
  map₂_left_unitor := Implementation.mapPseudoCone.pseudofunctor.map₂.leftUnitor K
  map₂_right_unitor := Implementation.mapPseudoCone.pseudofunctor.map₂.rightUnitor K

/-- The object action of pseudocone transport is `mapPseudoCone`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.obj {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    (mapPseudoCone.pseudofunctor K E).obj S = mapPseudoCone K S := sorry

/-- The `1`-morphism action of pseudocone transport is `mapPseudoCone.map`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.map {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    (mapPseudoCone.pseudofunctor K E).map u = mapPseudoCone.map K u := sorry

/-- The `2`-morphism action of pseudocone transport is `mapPseudoCone.map₂`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.map₂ {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E}
    {u v : S ⟶ T} (η : u ⟶ v) :
    (mapPseudoCone.pseudofunctor K E).map₂ η =
      mapPseudoCone.map₂ K η := sorry

/-- The unit comparison of pseudocone transport is `mapPseudoCone.mapId`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.mapId {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    (mapPseudoCone.pseudofunctor K E).mapId S =
      mapPseudoCone.mapId K S := sorry

/-- The composition comparison of pseudocone transport is `mapPseudoCone.mapComp`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.mapComp {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    (mapPseudoCone.pseudofunctor K E).mapComp u v =
      mapPseudoCone.mapComp K u v := sorry

-- Data audit: the object, `1`-morphism, and `2`-morphism actions and both comparison isomorphisms
-- are the explicit constructions imported above. The `sorryAx` dependency is confined to their
-- law, compatibility, coherence, and computation propositions.

end Pseudofunctor

end CategoryTheory
