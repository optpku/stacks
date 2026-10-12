/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Functoriality.Identity

/-!
# The pseudofunctor transporting readable pseudopullback cones

This module assembles object, morphism, and `2`-morphism transport together with its identity,
composition, and bicategorical coherence data. Projection-level computations are kept in a
separate downstream module.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace Implementation

/-- Mapping readable pseudopullback-cone `2`-morphisms preserves identities. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.id (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    mapPseudoPullbackCone.map₂ H (𝟙 u) =
      𝟙 (mapPseudoPullbackCone.map H u) := sorry

/-- Mapping readable pseudopullback-cone `2`-morphisms preserves vertical composition. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.comp (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} {u v w : S ⟶ T}
    (η : u ⟶ v) (θ : v ⟶ w) :
    mapPseudoPullbackCone.map₂ H (η ≫ θ) =
      mapPseudoPullbackCone.map₂ H η ≫
        mapPseudoPullbackCone.map₂ H θ := sorry

/-- The explicit prelax core for transport of readable pseudopullback cones. -/
private def mapPseudoPullbackCone.pseudofunctor.prelax (H : Pseudofunctor B D) :
    PrelaxFunctor (Bicategory.PseudoPullbackCone f g)
      (Bicategory.PseudoPullbackCone (H.map f) (H.map g)) where
  obj := mapPseudoPullbackCone H
  map := mapPseudoPullbackCone.map H
  map₂ := mapPseudoPullbackCone.map₂ H
  map₂_id := mapPseudoPullbackCone.pseudofunctor.map₂.id H
  map₂_comp := mapPseudoPullbackCone.pseudofunctor.map₂.comp H

/-- Readable pseudopullback-cone transport preserves left whiskering up to its explicit
composition comparisons. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.whiskerLeft
    (H : Pseudofunctor B D) :
    ∀ {R S T : Bicategory.PseudoPullbackCone f g} (u : R ⟶ S)
      {v w : S ⟶ T} (η : v ⟶ w),
      (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ (u ◁ η) =
        (mapPseudoPullbackCone.mapComp H u v).hom ≫
          (mapPseudoPullbackCone.pseudofunctor.prelax H).map u ◁
            (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ η ≫
          (mapPseudoPullbackCone.mapComp H u w).inv := sorry

/-- Readable pseudopullback-cone transport preserves right whiskering up to its explicit
composition comparisons. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.whiskerRight
    (H : Pseudofunctor B D) :
    ∀ {R S T : Bicategory.PseudoPullbackCone f g} {u v : R ⟶ S}
      (η : u ⟶ v) (w : S ⟶ T),
      (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ (η ▷ w) =
        (mapPseudoPullbackCone.mapComp H u w).hom ≫
          (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ η ▷
            (mapPseudoPullbackCone.pseudofunctor.prelax H).map w ≫
          (mapPseudoPullbackCone.mapComp H v w).inv := sorry

/-- Readable pseudopullback-cone transport preserves associators. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.associator
    (H : Pseudofunctor B D) :
    ∀ {Q R S T : Bicategory.PseudoPullbackCone f g}
      (u : Q ⟶ R) (v : R ⟶ S) (w : S ⟶ T),
      (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ (α_ u v w).hom =
        (mapPseudoPullbackCone.mapComp H (u ≫ v) w).hom ≫
          (mapPseudoPullbackCone.mapComp H u v).hom ▷
            (mapPseudoPullbackCone.pseudofunctor.prelax H).map w ≫
          (α_ ((mapPseudoPullbackCone.pseudofunctor.prelax H).map u)
            ((mapPseudoPullbackCone.pseudofunctor.prelax H).map v)
            ((mapPseudoPullbackCone.pseudofunctor.prelax H).map w)).hom ≫
          (mapPseudoPullbackCone.pseudofunctor.prelax H).map u ◁
            (mapPseudoPullbackCone.mapComp H v w).inv ≫
          (mapPseudoPullbackCone.mapComp H u (v ≫ w)).inv := sorry

/-- Readable pseudopullback-cone transport preserves left unitors. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.leftUnitor
    (H : Pseudofunctor B D) :
    ∀ {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T),
      (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ (λ_ u).hom =
        (mapPseudoPullbackCone.mapComp H (𝟙 S) u).hom ≫
          (mapPseudoPullbackCone.mapId H S).hom ▷
            (mapPseudoPullbackCone.pseudofunctor.prelax H).map u ≫
          (λ_ ((mapPseudoPullbackCone.pseudofunctor.prelax H).map u)).hom := sorry

/-- Readable pseudopullback-cone transport preserves right unitors. -/
private theorem mapPseudoPullbackCone.pseudofunctor.map₂.rightUnitor
    (H : Pseudofunctor B D) :
    ∀ {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T),
      (mapPseudoPullbackCone.pseudofunctor.prelax H).map₂ (ρ_ u).hom =
        (mapPseudoPullbackCone.mapComp H u (𝟙 T)).hom ≫
          (mapPseudoPullbackCone.pseudofunctor.prelax H).map u ◁
            (mapPseudoPullbackCone.mapId H T).hom ≫
          (ρ_ ((mapPseudoPullbackCone.pseudofunctor.prelax H).map u)).hom := sorry

end Implementation

variable (f) (g) in
/-- Mapping readable pseudopullback cones along `H` is a pseudofunctor.

This is the walking-cospan facade for generic pseudocone transport. Its object action is the
four-field square `mapPseudoPullbackCone`, while morphism comparisons are obtained from the
generic construction through the canonical presentation conjugations. The source cospan legs
are explicit because `H` alone does not determine the source cone bicategory. -/
def mapPseudoPullbackCone.pseudofunctor (H : Pseudofunctor B D) :
    Pseudofunctor (Bicategory.PseudoPullbackCone f g)
      (Bicategory.PseudoPullbackCone (H.map f) (H.map g)) where
  toPrelaxFunctor := Implementation.mapPseudoPullbackCone.pseudofunctor.prelax H
  mapId := mapPseudoPullbackCone.mapId H
  mapComp := mapPseudoPullbackCone.mapComp H
  map₂_whisker_left :=
    Implementation.mapPseudoPullbackCone.pseudofunctor.map₂.whiskerLeft H
  map₂_whisker_right :=
    Implementation.mapPseudoPullbackCone.pseudofunctor.map₂.whiskerRight H
  map₂_associator :=
    Implementation.mapPseudoPullbackCone.pseudofunctor.map₂.associator H
  map₂_left_unitor :=
    Implementation.mapPseudoPullbackCone.pseudofunctor.map₂.leftUnitor H
  map₂_right_unitor :=
    Implementation.mapPseudoPullbackCone.pseudofunctor.map₂.rightUnitor H

/-- The object action of readable pseudopullback-cone transport is
`mapPseudoPullbackCone`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.obj (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.pseudofunctor f g H).obj S =
      H.mapPseudoPullbackCone S := sorry

/-- The `1`-morphism action of readable pseudopullback-cone transport is
`mapPseudoPullbackCone.map`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g} (u : S ⟶ T) :
    (mapPseudoPullbackCone.pseudofunctor f g H).map u =
      mapPseudoPullbackCone.map H u := sorry

/-- The `2`-morphism action of readable pseudopullback-cone transport is
`mapPseudoPullbackCone.map₂`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.map₂ (H : Pseudofunctor B D)
    {S T : Bicategory.PseudoPullbackCone f g}
    {u v : S ⟶ T} (η : u ⟶ v) :
    (mapPseudoPullbackCone.pseudofunctor f g H).map₂ η =
      mapPseudoPullbackCone.map₂ H η := sorry

/-- The unit comparison of readable pseudopullback-cone transport is
`mapPseudoPullbackCone.mapId`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.mapId (H : Pseudofunctor B D)
    (S : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.pseudofunctor f g H).mapId S =
      mapPseudoPullbackCone.mapId H S := sorry

/-- The composition comparison of readable pseudopullback-cone transport is
`mapPseudoPullbackCone.mapComp`. -/
@[simp]
theorem mapPseudoPullbackCone.pseudofunctor.mapComp (H : Pseudofunctor B D)
    {R S T : Bicategory.PseudoPullbackCone f g}
    (u : R ⟶ S) (v : S ⟶ T) :
    (mapPseudoPullbackCone.pseudofunctor f g H).mapComp u v =
      mapPseudoPullbackCone.mapComp H u v := sorry

-- Data audit: the object, `1`-morphism, and `2`-morphism actions and both comparison
-- isomorphisms are the explicit constructions imported above. The `sorryAx` dependency is
-- confined to law, naturality, compatibility, coherence, and computation propositions.

end Pseudofunctor

end CategoryTheory
