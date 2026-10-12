/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Basic

/-!
# Action of the inertia pseudofunctor on stacks

The strict pseudofunctor is the data owner. This leaf exposes its action through the public
`inertia.map`, `inertia.map₂`, and local Hom-functor interfaces.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.inertia

variable {X Y : StackOver.{u, v, w, vS} J}

/-- The action of stack inertia on a `1`-morphism, projected directly from its strict
pseudofunctor owner. -/
@[stacks 04Z4 "stack absolute-inertia map"]
def map (F : X ⟶ Y) : StackOver.inertia X ⟶ StackOver.inertia Y :=
  (StackOver.Inertia.strictPseudofunctor J).map F

/-- The action of stack inertia on a `2`-morphism, projected directly from its strict
pseudofunctor owner. -/
@[stacks 04Z4 "stack absolute-inertia action on 2-morphisms"]
def map₂ {F G : X ⟶ Y} (eta : F ⟶ G) : map F ⟶ map G :=
  (StackOver.Inertia.strictPseudofunctor J).map₂ eta

/-- Stack inertia acts functorially on every local Hom category. -/
@[stacks 04Z4 "stack absolute-inertia local hom functor"]
def mapFunctor (X Y : StackOver.{u, v, w, vS} J) :
    (X ⟶ Y) ⥤ (StackOver.inertia X ⟶ StackOver.inertia Y) :=
  (StackOver.Inertia.strictPseudofunctor J).mapFunctor X Y

/-- The ambient fibred morphism underlying a stack inertia map is the canonical neutral
fibred-inertia map. -/
@[simp]
theorem map.hom (F : X ⟶ Y) :
    Hom.toMor (map F) = FiberedCategoryOver.Inertia.map (Hom.toMor F) := sorry

/-- The ambient `2`-morphism underlying a stack inertia `2`-cell is the strict neutral
fibred-inertia action. -/
@[simp]
theorem map₂.hom {F G : X ⟶ Y} (eta : F ⟶ G) :
    Hom.toMor₂ (map₂ eta) =
      (FiberedCategoryOver.Inertia.strictPseudofunctor C).map₂ (Hom.toMor₂ eta) := sorry

/-- The stack inertia action preserves identity `1`-morphisms strictly. -/
@[simp]
theorem map.id (X : StackOver.{u, v, w, vS} J) :
    map (𝟙 X) = 𝟙 (StackOver.inertia X) := sorry

/-- The stack inertia action preserves horizontal composition strictly. -/
@[simp]
theorem map.comp
    {Z : StackOver.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

/-- The stack inertia action preserves identity `2`-morphisms. -/
@[simp]
theorem map₂.id (F : X ⟶ Y) : map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- The stack inertia action preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ (eta ≫ theta) = map₂ eta ≫ map₂ theta := sorry

/-- The object action of the local stack inertia functor is `inertia.map`. -/
@[simp]
theorem mapFunctor.obj (F : X ⟶ Y) : (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the local stack inertia functor is `inertia.map₂`. -/
@[simp]
theorem mapFunctor.map {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor X Y).map eta = map₂ eta := sorry

end StackOver.inertia

end CategoryTheory
