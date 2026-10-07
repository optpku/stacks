module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Associativity of categorical pullbacks

An explicit reassociation equivalence between the two iterated categorical pullbacks of a
four-legged zigzag.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

namespace Limits.CategoricalPullback

variable (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D)

-- Local declaration justification (source-local notation): this file implements one fixed
-- rebracketing equivalence. The two names keep the exact source and target presentations shared
-- by its private object/map data and coherence fields. They have no construction independent of
-- this four-legged cospan, and every exported declaration elaborates to the underlying
-- `CategoricalPullback` expression; a public type alias would only duplicate the endpoints of
-- `associativity` rather than provide an operation for a separate consumer.
local notation "LeftAssociated" => (((π₂ F G) ⋙ H) ⊡ I)
local notation "RightAssociated" => (F ⊡ ((π₁ H I) ⋙ G))

namespace Associator

/- Import decisions:
- `Categorical.Basic` is public because the exported reassociation functors and equivalence expose
  categorical pullbacks, their projections, and their morphisms. -/

/- This is the categorical-pullback analogue of `CategoryTheory.prod.associativity`. Mathlib's
`CategoricalPullback.functorEquiv` describes a single cospan cone, while
`CatCospanTransform.associator` reassociates composites of cospan transformations; neither has
these two nested categorical-pullback models as endpoints. The explicit construction here is
therefore the canonical owner.
It changes only the bracketing of the three visible entries. Ordinary `def`s are intentional:
the two maps are definitionally inverse after unfolding, as for the product associator, but this
implementation detail need not be forced transparent across module boundaries by `abbrev`. -/

section AssociativityImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Rebracket an object of an iterated categorical pullback from left to right:
`((a, c, φ), e, ψ) ↦ (a, (c, e, ψ), φ)`. -/
private def forwardObj (X : LeftAssociated) : RightAssociated where
  fst := X.fst.fst
  snd :=
    { fst := X.fst.snd
      snd := X.snd
      iso := X.iso }
  iso := X.fst.iso

/-- Rebracket a morphism of an iterated categorical pullback componentwise from left to right. -/
private def forwardMap {X Y : LeftAssociated} (f : X ⟶ Y) :
    forwardObj F G H I X ⟶ forwardObj F G H I Y where
  fst := f.fst.fst
  snd :=
    { fst := f.fst.snd
      snd := f.snd
      w := f.w }
  w := f.fst.w

/-- `forwardMap` preserves identity morphisms. -/
private theorem forwardMapId (X : LeftAssociated) :
    forwardMap F G H I (𝟙 X) = 𝟙 (forwardObj F G H I X) := sorry
/- Proof strategy: apply nested `CategoricalPullback.hom_ext`; the three visible components are
identity morphisms, so each remaining equality is reflexive. -/

/-- `forwardMap` preserves composition of morphisms. -/
private theorem forwardMapComp {X Y Z : LeftAssociated} (f : X ⟶ Y) (g : Y ⟶ Z) :
    forwardMap F G H I (f ≫ g) =
      forwardMap F G H I f ≫ forwardMap F G H I g := sorry
/- Proof strategy: apply nested `CategoricalPullback.hom_ext`; all three components reduce to
composition in `A`, `C`, and `E`. -/

end Implementation

/-- The canonical forward functor rebracketing an iterated categorical pullback from left to
right. -/
def forward : LeftAssociated ⥤ RightAssociated where
  obj := Implementation.forwardObj F G H I
  map := Implementation.forwardMap F G H I
  map_id := Implementation.forwardMapId F G H I
  map_comp := Implementation.forwardMapComp F G H I

namespace Implementation

/-- Rebracket an object of an iterated categorical pullback from right to left:
`(a, (c, e, ψ), φ) ↦ ((a, c, φ), e, ψ)`. -/
private def inverseObj (X : RightAssociated) : LeftAssociated where
  fst :=
    { fst := X.fst
      snd := X.snd.fst
      iso := X.iso }
  snd := X.snd.snd
  iso := X.snd.iso

/-- Rebracket a morphism of an iterated categorical pullback componentwise from right to left. -/
private def inverseMap {X Y : RightAssociated} (f : X ⟶ Y) :
    inverseObj F G H I X ⟶ inverseObj F G H I Y where
  fst :=
    { fst := f.fst
      snd := f.snd.fst
      w := f.w }
  snd := f.snd.snd
  w := f.snd.w

/-- `inverseMap` preserves identity morphisms. -/
private theorem inverseMapId (X : RightAssociated) :
    inverseMap F G H I (𝟙 X) =
      𝟙 (inverseObj F G H I X) := sorry
/- Proof strategy: apply nested `CategoricalPullback.hom_ext`; all three component equalities are
reflexive. -/

/-- `inverseMap` preserves composition of morphisms. -/
private theorem inverseMapComp {X Y Z : RightAssociated} (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseMap F G H I (f ≫ g) =
      inverseMap F G H I f ≫ inverseMap F G H I g := sorry
/- Proof strategy: apply nested `CategoricalPullback.hom_ext`; every component reduces to
composition in its ambient category. -/

end Implementation

/-- The canonical inverse functor rebracketing an iterated categorical pullback from right to
left. -/
def inverse : RightAssociated ⥤ LeftAssociated where
  obj := Implementation.inverseObj F G H I
  map := Implementation.inverseMap F G H I
  map_id := Implementation.inverseMapId F G H I
  map_comp := Implementation.inverseMapComp F G H I

end AssociativityImplementation

end Associator

end Limits.CategoricalPullback

end CategoryTheory
