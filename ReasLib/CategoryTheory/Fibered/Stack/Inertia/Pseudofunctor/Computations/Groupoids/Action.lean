/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Groupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Forgetful

/-!
# The action of groupoid-stack inertia

This file owns the local Hom action of groupoid-stack inertia and its forgetful computations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.inertia

variable {X Y : StackOver.Groupoids.{u, v, w, vS} J}

/-- The action of groupoid-stack inertia on a `1`-morphism. -/
@[stacks 04Z4 "groupoid-stack absolute-inertia map"]
def map (F : X ⟶ Y) :
    StackOver.Groupoids.inertia X ⟶ StackOver.Groupoids.inertia Y :=
  (StackOver.Groupoids.Inertia.strictPseudofunctor J).map F

/-- The action of groupoid-stack inertia on a `2`-morphism. -/
@[stacks 04Z4 "groupoid-stack absolute-inertia action on 2-morphisms"]
def map₂ {F G : X ⟶ Y} (eta : F ⟶ G) : map F ⟶ map G :=
  (StackOver.Groupoids.Inertia.strictPseudofunctor J).map₂ eta

/-- Groupoid-stack inertia acts functorially on every local Hom category. -/
@[stacks 04Z4 "groupoid-stack absolute-inertia local hom functor"]
def mapFunctor (X Y : StackOver.Groupoids.{u, v, w, vS} J) :
    (X ⟶ Y) ⥤
      (StackOver.Groupoids.inertia X ⟶ StackOver.Groupoids.inertia Y) :=
  (StackOver.Groupoids.Inertia.strictPseudofunctor J).mapFunctor X Y

/-- Forgetting a groupoid-stack inertia map gives the neutral groupoid-fibred action. -/
@[simp, stacks 04Z4 "underlying groupoid-fibred inertia map"]
theorem map.hom (F : X ⟶ Y) :
    Hom.toGroupoidsMor (map F) =
      (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).map
        (Hom.toGroupoidsMor F) := sorry

/-- The based functor underlying a groupoid-stack inertia map is the neutral inertia map. -/
@[simp, stacks 04Z4 "based groupoid-stack inertia map"]
theorem map.toBasedFunctor (F : X ⟶ Y) :
    Hom.toBasedFunctor (map F) = BasedCategory.Inertia.map (Hom.toBasedFunctor F) := sorry

/-- Forgetting a groupoid-stack inertia `2`-cell gives the neutral groupoid-fibred action. -/
@[simp, stacks 04Z4 "underlying groupoid-fibred inertia 2-cell"]
theorem map₂.hom {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ eta).hom =
      (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C).map₂ eta.hom := sorry

/-- The based natural transformation underlying a groupoid-stack inertia `2`-cell is the
neutral inertia action. -/
@[simp, stacks 04Z4 "based groupoid-stack inertia 2-cell"]
theorem map₂.toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    Hom₂.toBasedNatTrans (map₂ eta) =
      BasedCategory.Inertia.map₂ (Hom₂.toBasedNatTrans eta) := sorry

/-- The total-category natural transformation underlying a groupoid-stack inertia `2`-cell is
the neutral total inertia action. -/
@[simp, stacks 04Z4 "total groupoid-stack inertia 2-cell"]
theorem map₂.toNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    Hom₂.toNatTrans (map₂ eta) =
      (BasedCategory.Inertia.map₂ (Hom₂.toBasedNatTrans eta)).toNatTrans := sorry

/-- Groupoid-stack inertia preserves identity `1`-morphisms strictly. -/
@[simp]
theorem map.id (X : StackOver.Groupoids.{u, v, w, vS} J) :
    map (𝟙 X) = 𝟙 (StackOver.Groupoids.inertia X) := sorry

/-- Groupoid-stack inertia preserves horizontal composition strictly. -/
@[simp]
theorem map.comp
    {Z : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

/-- Groupoid-stack inertia preserves identity `2`-morphisms. -/
@[simp]
theorem map₂.id (F : X ⟶ Y) : map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Groupoid-stack inertia preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ (eta ≫ theta) = map₂ eta ≫ map₂ theta := sorry

/-- The object action of the local groupoid-stack inertia functor is `inertia.map`. -/
@[simp]
theorem mapFunctor.obj (F : X ⟶ Y) : (mapFunctor X Y).obj F = map F := sorry

/-- The morphism action of the local groupoid-stack inertia functor is `inertia.map₂`. -/
@[simp]
theorem mapFunctor.map {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor X Y).map eta = map₂ eta := sorry

end StackOver.Groupoids.inertia

end CategoryTheory
