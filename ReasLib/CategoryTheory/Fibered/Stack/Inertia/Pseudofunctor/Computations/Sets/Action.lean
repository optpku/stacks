/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Setoids
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Sets

/-!
# Local action of set-stack inertia

The named `1`-cell, `2`-cell, and local-Hom actions of the strict pseudofunctor, together with
readouts to the setoid-stack and based-category layers.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.inertia

variable {X Y : StackOver.Sets.{u, v, w, vS} J}

/-- The action of set-stack inertia on a `1`-morphism. -/
@[stacks 04Z4 "set-stack absolute-inertia map"]
def map (F : X ⟶ Y) : StackOver.Sets.inertia X ⟶ StackOver.Sets.inertia Y :=
  (StackOver.Sets.Inertia.strictPseudofunctor J).map F

/-- The action of set-stack inertia on a `2`-morphism. -/
@[stacks 04Z4 "set-stack absolute-inertia action on 2-morphisms"]
def map₂ {F G : X ⟶ Y} (eta : F ⟶ G) : map F ⟶ map G :=
  (StackOver.Sets.Inertia.strictPseudofunctor J).map₂ eta

/-- Set-stack inertia acts functorially on every local Hom category. -/
@[stacks 04Z4 "set-stack absolute-inertia local hom functor"]
def mapFunctor (X Y : StackOver.Sets.{u, v, w, vS} J) :
    (X ⟶ Y) ⥤ (StackOver.Sets.inertia X ⟶ StackOver.Sets.inertia Y) :=
  (StackOver.Sets.Inertia.strictPseudofunctor J).mapFunctor X Y

/-- The underlying setoid-stack morphism is the neutral inertia action. -/
@[simp]
theorem map.hom (F : X ⟶ Y) :
    (map F).hom =
      StackOver.Setoids.inertia.map (Hom.toSetoidsMor F) := sorry

/-- Forgetting to set-fibred categories gives the neutral inertia action directly. -/
@[simp, stacks 04Z4 "underlying set-fibred absolute-inertia map"]
theorem map.toSets (F : X ⟶ Y) :
    Hom.toSetsMor (map F) =
      (FiberedCategoryOver.Sets.Inertia.strictPseudofunctor C).map
        (Hom.toSetsMor F) := sorry

/-- The underlying setoid-stack `2`-cell is the setoid-stack inertia action. -/
@[simp]
theorem map₂.hom {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ eta).hom = StackOver.Setoids.inertia.map₂ eta.hom := sorry

/-- The based natural transformation underlying a set-stack inertia `2`-cell is the neutral
inertia action. -/
@[simp]
theorem map₂.toBased {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ eta).hom.hom.hom.hom =
      BasedCategory.Inertia.map₂ eta.hom.hom.hom.hom := sorry

/-- Set-stack inertia preserves identity `1`-morphisms strictly. -/
@[simp]
theorem map.id (X : StackOver.Sets.{u, v, w, vS} J) :
    map (𝟙 X) = 𝟙 (StackOver.Sets.inertia X) := sorry

/-- Set-stack inertia preserves horizontal composition strictly. -/
@[simp]
theorem map.comp
    {Z : StackOver.Sets.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

/-- Set-stack inertia preserves identity `2`-morphisms. -/
@[simp]
theorem map₂.id (F : X ⟶ Y) : map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Set-stack inertia preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ (eta ≫ theta) = map₂ eta ≫ map₂ theta := sorry

/-- The object action of the local inertia functor is `inertia.map`. -/
@[simp]
theorem mapFunctor.obj (F : X ⟶ Y) : (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the local inertia functor is `inertia.map₂`. -/
@[simp]
theorem mapFunctor.map {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor X Y).map eta = map₂ eta := sorry

end StackOver.Sets.inertia

end CategoryTheory
