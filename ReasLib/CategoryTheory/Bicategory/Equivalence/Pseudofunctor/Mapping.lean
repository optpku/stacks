module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Adjunction.Action

/-!
# Mapping bicategorical equivalences by pseudofunctors

This module owns the data-level pseudofunctorial action on bicategorical
equivalences: mapped units and counits, the mapped equivalence itself, and its
comparison with the canonical action on bicategorical adjunctions. Coherence
for identity, reversal, and composition is available in a sibling leaf.
-/

@[expose] public section

universe w v u w' v' u'

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Pseudofunctor

variable {C : Type u'} [Bicategory.{w', v'} C]
variable {x y : B}

/-- The unit isomorphism obtained by mapping the unit of a bicategorical equivalence through a
pseudofunctor.

The two pseudofunctor comparisons convert the mapped identity and mapped composite to the
identity and composite in the target bicategory. -/
@[stacks 0040 "mapped unit of a bicategorical equivalence"]
def mapEquivalence.unitIso (F : Pseudofunctor B C) (e : x ≌ y) :
    𝟙 (F.obj x) ≅ F.map e.hom ≫ F.map e.inv :=
  (F.mapId x).symm ≪≫ F.map₂Iso e.unit ≪≫
    F.mapComp e.hom e.inv

/-- The counit isomorphism obtained by mapping the counit of a bicategorical equivalence through
a pseudofunctor. -/
@[stacks 0040 "mapped counit of a bicategorical equivalence"]
def mapEquivalence.counitIso (F : Pseudofunctor B C) (e : x ≌ y) :
    F.map e.inv ≫ F.map e.hom ≅ 𝟙 (F.obj y) :=
  (F.mapComp e.inv e.hom).symm ≪≫
    F.map₂Iso e.counit ≪≫ F.mapId y

/-- The forward cell of the mapped unit is the mapped original unit between the two
pseudofunctor comparison cells. -/
@[simp]
theorem mapEquivalence.unitIso.hom
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.unitIso F e).hom =
      (F.mapId x).inv ≫ F.map₂ e.unit.hom ≫
        (F.mapComp e.hom e.inv).hom := sorry
/- Proof strategy: unfold `mapEquivalence.unitIso` and use the hom projections of composite
isomorphisms and `Pseudofunctor.map₂Iso`. -/

/-- The inverse cell of the mapped unit is the mapped inverse unit between the inverse
pseudofunctor comparison cells. -/
@[simp]
theorem mapEquivalence.unitIso.inv
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.unitIso F e).inv =
      (F.mapComp e.hom e.inv).inv ≫ F.map₂ e.unit.inv ≫
        (F.mapId x).hom := sorry
/- Proof strategy: unfold `mapEquivalence.unitIso` and use the inverse projections of composite
isomorphisms and `Pseudofunctor.map₂Iso`. -/

/-- The forward cell of the mapped counit is the mapped original counit between the two
pseudofunctor comparison cells. -/
@[simp]
theorem mapEquivalence.counitIso.hom
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.counitIso F e).hom =
      (F.mapComp e.inv e.hom).inv ≫ F.map₂ e.counit.hom ≫
        (F.mapId y).hom := sorry
/- Proof strategy: unfold `mapEquivalence.counitIso` and use the hom projections of composite
isomorphisms and `Pseudofunctor.map₂Iso`. -/

/-- The inverse cell of the mapped counit is the mapped inverse counit between the inverse
pseudofunctor comparison cells. -/
@[simp]
theorem mapEquivalence.counitIso.inv
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (mapEquivalence.counitIso F e).inv =
      (F.mapId y).inv ≫ F.map₂ e.counit.inv ≫
        (F.mapComp e.inv e.hom).hom := sorry
/- Proof strategy: unfold `mapEquivalence.counitIso` and use the inverse projections of composite
isomorphisms and `Pseudofunctor.map₂Iso`. -/

/-- The mapped unit and counit satisfy the bicategorical left triangle identity. -/
theorem mapEquivalence.left_triangle
    (F : Pseudofunctor B C) (e : x ≌ y) :
    leftZigzagIso (mapEquivalence.unitIso F e)
        (mapEquivalence.counitIso F e) =
      λ_ (F.map e.hom) ≪≫ (ρ_ (F.map e.hom)).symm := sorry
/- Proof strategy: take homs of both sides, identify them with the left triangle of
`F.mapAdjunction e.toAdjunction`, and use that every constituent of the mapped unit and counit is
invertible. -/

/-- A pseudofunctor maps a bicategorical equivalence to a bicategorical equivalence.

This is the invertible refinement of `Pseudofunctor.mapAdjunction`; its unit and counit retain
the canonical mapped isomorphisms rather than choosing new adjoint-equivalence data. -/
@[stacks 0040 "map a bicategorical equivalence through a pseudofunctor"]
def mapEquivalence (F : Pseudofunctor B C) (e : x ≌ y) :
    F.obj x ≌ F.obj y where
  hom := F.map e.hom
  inv := F.map e.inv
  unit := mapEquivalence.unitIso F e
  counit := mapEquivalence.counitIso F e
  left_triangle := mapEquivalence.left_triangle F e

/-- The forward morphism of a mapped equivalence is the image of the original forward
morphism. -/
@[simp]
theorem mapEquivalence.hom (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).hom = F.map e.hom := sorry
/- Proof strategy: unfold `mapEquivalence` and read its forward-morphism field. -/

/-- The inverse morphism of a mapped equivalence is the image of the original inverse
morphism. -/
@[simp]
theorem mapEquivalence.inv (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).inv = F.map e.inv := sorry
/- Proof strategy: unfold `mapEquivalence` and read its inverse-morphism field. -/

/-- The unit of a mapped equivalence is the canonical mapped unit isomorphism. -/
@[simp]
theorem mapEquivalence.unit (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).unit = mapEquivalence.unitIso F e := sorry
/- Proof strategy: unfold `mapEquivalence` and read its unit field. -/

/-- The counit of a mapped equivalence is the canonical mapped counit isomorphism. -/
@[simp]
theorem mapEquivalence.counit (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).counit = mapEquivalence.counitIso F e := sorry
/- Proof strategy: unfold `mapEquivalence` and read its counit field. -/

/-- Forgetting invertibility from a mapped equivalence recovers the canonical mapped
adjunction. -/
@[simp]
theorem mapEquivalence.toAdjunction
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).toAdjunction =
      F.mapAdjunction e.toAdjunction := sorry
/- Proof strategy: extensionality reduces the statement to the hom components of
`mapEquivalence.unitIso` and `mapEquivalence.counitIso`, which are the unit and counit used by
`Pseudofunctor.mapAdjunction`. -/

/-- Passing a mapped equivalence to `Bicategory.Adj` agrees with applying the canonical
`mapAdj` action to the original underlying adjunction. -/
@[simp]
theorem mapEquivalence.toAdjHom
    (F : Pseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).toAdjHom =
      F.mapAdj.map e.toAdjHom := sorry

/- Data audit (mathlib 4.32): `mapEquivalence.unitIso`, `mapEquivalence.counitIso`, and
`mapEquivalence` expose the mapped forward and inverse morphisms and both directions of the
mapped unit and counit explicitly. Their `sorryAx` is confined to the Prop-valued triangle
field; the comparison maps used in the data come from `Pseudofunctor.mapAdj`. -/

end Pseudofunctor

end CategoryTheory
