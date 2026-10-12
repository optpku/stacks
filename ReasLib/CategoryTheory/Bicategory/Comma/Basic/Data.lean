/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Colax comma data

This leaf owns the non-Prop data for the reusable two-sided colax comma
construction `Bicategory.ColaxComma F G`: its objects, `1`-morphisms, and
`2`-morphisms. The bicategory assembly and componentwise computation API are
provided by `Comma.Basic.Bicategory` and `Comma.Basic.Computation`.
-/

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- The colax comma object of pseudofunctors `F : A ⥤ᵖ C` and `G : B ⥤ᵖ C`.

An object consists of `a : A`, `b : B`, and a `1`-morphism
`hom : F.obj a ⟶ G.obj b`. This is the object layer of the bicategorical comma
construction; costructured arrows and slices are specializations, not independent
root definitions.

The comma datum is therefore the displayed arrow `hom : F.obj a ⟶ G.obj b`; the words
“left endpoint”, “right endpoint”, and “comparison arrow” describe all of its non-Prop data. -/
@[stacks 003Q "two-sided colax comma data", ext]
structure ColaxComma.Object (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) where
  /-- The object on the domain side of the comma diagram. -/
  left : A
  /-- The object on the codomain side of the comma diagram. -/
  right : B
  /-- The structural `1`-morphism between the two pseudofunctor values. -/
  hom : F.obj left ⟶ G.obj right

/-- The canonical categorical colax comma carrier associated to an explicit presentation. -/
def ColaxComma (F : A ⥤ᵖ C) (G : B ⥤ᵖ C) := ColaxComma.Object F G

namespace ColaxComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

/-- Construct a colax comma object from its two endpoints and displayed arrow. -/
def Object.ofComponents (left : A) (right : B) (hom : F.obj left ⟶ G.obj right) :
    ColaxComma.Object F G := ⟨left, right, hom⟩

/-- Construct the canonical colax comma carrier from its displayed components. -/
def mk (left : A) (right : B) (hom : F.obj left ⟶ G.obj right) : ColaxComma F G :=
  Object.ofComponents left right hom

/-- The left endpoint of a colax comma object. -/
def left (S : ColaxComma F G) : A := Object.left S

/-- The right endpoint of a colax comma object. -/
def right (S : ColaxComma F G) : B := Object.right S

/-- The displayed arrow of a colax comma object. -/
def hom (S : ColaxComma F G) : F.obj S.left ⟶ G.obj S.right := Object.hom S

/-- Equality of colax comma objects is determined by their displayed components. -/
@[ext (iff := false)]
theorem ext {S T : ColaxComma F G} (hleft : S.left = T.left) (hright : S.right = T.right)
    (hhom : S.hom = hleft ▸ hright ▸ T.hom) : S = T := by
  cases S
  cases T
  cases hleft
  cases hright
  cases hhom
  rfl

/-- A `1`-morphism in a colax comma bicategory.

Besides maps on the two endpoints, it carries a comparison `2`-morphism from the
upper-right composite to the lower-left composite:

```
                              F.map left
       F.obj S.left ─────────────────────────▶ F.obj T.left
              │                  ⇓ cell               │
        S.hom │                                       │ T.hom
              ▼                                       ▼
       G.obj S.right ────────────────────────▶ G.obj T.right
                              G.map right
```

Thus `cell : F.map left ≫ T.hom ⟶ S.hom ≫ G.map right`. Under the convention
used by nLab and Johnson--Yau this is the colax, rather than lax, orientation. -/
@[ext]
structure Morphism (S T : ColaxComma F G) where
  /-- The map between the left endpoints. -/
  left : S.left ⟶ T.left
  /-- The map between the right endpoints. -/
  right : S.right ⟶ T.right
  /-- The colax comparison `2`-morphism. -/
  cell : F.map left ≫ T.hom ⟶ S.hom ≫ G.map right

/-- Construct an explicit colax comma morphism from its endpoint maps and comparison cell. -/
def Morphism.ofComponents {S T : ColaxComma F G} (left : S.left ⟶ T.left)
    (right : S.right ⟶ T.right)
    (cell : F.map left ≫ T.hom ⟶ S.hom ≫ G.map right) : Morphism S T :=
  ⟨left, right, cell⟩

/-- The canonical categorical hom carrier associated to an explicit morphism presentation. -/
def Hom (S T : ColaxComma F G) := Morphism S T

namespace Hom

/-- Construct the canonical colax comma morphism from its three displayed components. -/
def mk {S T : ColaxComma F G} (left : S.left ⟶ T.left) (right : S.right ⟶ T.right)
    (cell : F.map left ≫ T.hom ⟶ S.hom ≫ G.map right) : Hom S T :=
  Morphism.ofComponents left right cell

/-- Construct a colax comma `1`-morphism from its three components. -/
def ofComponents {S T : ColaxComma F G} (left : S.left ⟶ T.left)
    (right : S.right ⟶ T.right)
    (cell : F.map left ≫ T.hom ⟶ S.hom ≫ G.map right) : Hom S T :=
  mk left right cell

/-- The left endpoint map of a colax comma `1`-morphism. -/
def left {S T : ColaxComma F G} (f : Hom S T) : S.left ⟶ T.left := Morphism.left f

/-- The right endpoint map of a colax comma `1`-morphism. -/
def right {S T : ColaxComma F G} (f : Hom S T) : S.right ⟶ T.right := Morphism.right f

/-- The comparison cell of a colax comma `1`-morphism. -/
def cell {S T : ColaxComma F G} (f : Hom S T) : F.map f.left ≫ T.hom ⟶ S.hom ≫ G.map f.right :=
  Morphism.cell f

/-- Equality of colax comma `1`-morphisms is determined by their displayed components. -/
@[ext (iff := false)]
theorem ext {S T : ColaxComma F G} {f g : Hom S T} (hleft : f.left = g.left)
    (hright : f.right = g.right) (hcell : f.cell = hleft ▸ hright ▸ g.cell) : f = g := by
  cases f
  cases g
  cases hleft
  cases hright
  cases hcell
  rfl

end Hom

/-- A `2`-morphism of colax comma `1`-morphisms consists of compatible cells on
the two endpoint maps. -/
@[ext]
structure Cell {S T : ColaxComma F G} (f g : Hom S T) where
  /-- The `2`-morphism between the left endpoint maps. -/
  left : f.left ⟶ g.left
  /-- The `2`-morphism between the right endpoint maps. -/
  right : f.right ⟶ g.right
  /-- Compatibility with the two comma comparison cells. -/
  w : (F.map₂ left ▷ T.hom) ≫ g.cell =
    f.cell ≫ (S.hom ◁ G.map₂ right)

/-- Construct an explicit colax comma cell from its endpoint cells and compatibility proof. -/
def Cell.ofComponents {S T : ColaxComma F G} {f g : Hom S T} (left : f.left ⟶ g.left)
    (right : f.right ⟶ g.right)
    (w : (F.map₂ left ▷ T.hom) ≫ g.cell = f.cell ≫ (S.hom ◁ G.map₂ right)) : Cell f g :=
  ⟨left, right, w⟩

/-- The canonical categorical `2`-morphism carrier associated to an explicit cell presentation. -/
def Hom₂ {S T : ColaxComma F G} (f g : Hom S T) := Cell f g

namespace Hom₂

/-- Construct the canonical colax comma cell from its endpoint cells and compatibility proof. -/
def mk {S T : ColaxComma F G} {f g : Hom S T} (left : f.left ⟶ g.left)
    (right : f.right ⟶ g.right)
    (w : (F.map₂ left ▷ T.hom) ≫ g.cell = f.cell ≫ (S.hom ◁ G.map₂ right)) : Hom₂ f g :=
  Cell.ofComponents left right w

/-- Construct a colax comma `2`-morphism from its endpoint cells and compatibility proof. -/
def ofComponents {S T : ColaxComma F G} {f g : Hom S T} (left : f.left ⟶ g.left)
    (right : f.right ⟶ g.right)
    (w : (F.map₂ left ▷ T.hom) ≫ g.cell = f.cell ≫ (S.hom ◁ G.map₂ right)) : Hom₂ f g :=
  mk left right w

/-- The left endpoint cell of a colax comma `2`-morphism. -/
def left {S T : ColaxComma F G} {f g : Hom S T} (η : Hom₂ f g) : f.left ⟶ g.left := Cell.left η

/-- The right endpoint cell of a colax comma `2`-morphism. -/
def right {S T : ColaxComma F G} {f g : Hom S T} (η : Hom₂ f g) : f.right ⟶ g.right := Cell.right η

/-- The compatibility equation of a colax comma `2`-morphism. -/
theorem w {S T : ColaxComma F G} {f g : Hom S T} (η : Hom₂ f g) :
    (F.map₂ η.left ▷ T.hom) ≫ g.cell = f.cell ≫ (S.hom ◁ G.map₂ η.right) := Cell.w η

/-- Equality of colax comma `2`-morphisms is determined by their endpoint cells. -/
@[ext]
theorem ext {S T : ColaxComma F G} {f g : Hom S T} {η θ : Hom₂ f g}
    (hleft : η.left = θ.left) (hright : η.right = θ.right) : η = θ := by
  cases η
  cases θ
  cases hleft
  cases hright
  rfl

end Hom₂

end ColaxComma
end Bicategory
end CategoryTheory
