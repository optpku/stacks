/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Groupoids
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Setoids
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Forgetful

/-!
# The action of setoid-stack inertia

This file owns the local Hom action of setoid-stack inertia and its forgetful computations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.inertia

variable {X Y : StackOver.Setoids.{u, v, w, vS} J}

/-- The action of setoid-stack inertia on a `1`-morphism. -/
@[stacks 04Z4 "setoid-stack absolute-inertia map"]
def map (F : X ⟶ Y) :
    StackOver.Setoids.inertia X ⟶ StackOver.Setoids.inertia Y :=
  (StackOver.Setoids.Inertia.strictPseudofunctor J).map F

/-- The action of setoid-stack inertia on a `2`-morphism. -/
@[stacks 04Z4 "setoid-stack absolute-inertia action on 2-morphisms"]
def map₂ {F G : X ⟶ Y} (eta : F ⟶ G) : map F ⟶ map G :=
  (StackOver.Setoids.Inertia.strictPseudofunctor J).map₂ eta

/-- Setoid-stack inertia acts functorially on every local Hom category. -/
@[stacks 04Z4 "setoid-stack absolute-inertia local hom functor"]
def mapFunctor (X Y : StackOver.Setoids.{u, v, w, vS} J) :
    (X ⟶ Y) ⥤ (StackOver.Setoids.inertia X ⟶ StackOver.Setoids.inertia Y) :=
  (StackOver.Setoids.Inertia.strictPseudofunctor J).mapFunctor X Y

/-- Forgetting thinness from a setoid-stack inertia map gives the groupoid-stack action. -/
@[simp, stacks 04Z4 "underlying groupoid-stack inertia map"]
theorem map.hom (F : X ⟶ Y) :
    Hom.toGroupoidsMor (map F) =
      StackOver.Groupoids.inertia.map (Hom.toGroupoidsMor F) := sorry

/-- Forgetting directly to setoid-fibred categories gives the neutral inertia action. -/
@[simp, stacks 04Z4 "underlying setoid-fibred inertia map"]
theorem map.toSetoidsMor (F : X ⟶ Y) :
    Hom.toSetoidsMor (map F) =
      (FiberedCategoryOver.Setoids.Inertia.strictPseudofunctor C).map
        (Hom.toSetoidsMor F) := sorry

/-- Forgetting thinness from a setoid-stack inertia `2`-cell gives the groupoid-stack action. -/
@[simp, stacks 04Z4 "underlying groupoid-stack inertia 2-cell"]
theorem map₂.hom {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ eta).hom = StackOver.Groupoids.inertia.map₂ eta.hom := sorry

/-- The based natural transformation underlying a setoid-stack inertia `2`-cell is the neutral
inertia action. -/
@[simp, stacks 04Z4 "based setoid-stack inertia 2-cell"]
theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    Hom₂.toBasedNatTrans (map₂ eta) =
      BasedCategory.Inertia.map₂ (Hom₂.toBasedNatTrans eta) := sorry

/-- The total-category natural transformation underlying a setoid-stack inertia `2`-cell is
the neutral total inertia action. -/
@[simp, stacks 04Z4 "total setoid-stack inertia 2-cell"]
theorem map₂.toNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    Hom₂.toNatTrans (map₂ eta) =
      (BasedCategory.Inertia.map₂ (Hom₂.toBasedNatTrans eta)).toNatTrans := sorry

/-- Setoid-stack inertia preserves identity `1`-morphisms strictly. -/
@[simp]
theorem map.id (X : StackOver.Setoids.{u, v, w, vS} J) :
    map (𝟙 X) = 𝟙 (StackOver.Setoids.inertia X) := sorry

/-- Setoid-stack inertia preserves horizontal composition strictly. -/
@[simp]
theorem map.comp
    {Z : StackOver.Setoids.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

/-- Setoid-stack inertia preserves identity `2`-morphisms. -/
@[simp]
theorem map₂.id (F : X ⟶ Y) : map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Setoid-stack inertia preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ (eta ≫ theta) = map₂ eta ≫ map₂ theta := sorry

/-- The object action of the local setoid-stack inertia functor is `inertia.map`. -/
@[simp]
theorem mapFunctor.obj (F : X ⟶ Y) : (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the local setoid-stack inertia functor is `inertia.map₂`. -/
@[simp]
theorem mapFunctor.map {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor X Y).map eta = map₂ eta := sorry

end StackOver.Setoids.inertia

end CategoryTheory
