/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements.Forward
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence

/-!
# Stacks in sets of algebraic spaces and their universe alignment

The fppf sheaf of points of an algebraic space determines a stack in sets over the scheme
base. Morphisms of algebraic spaces induce cartesian morphisms between these stacks.
Bundled two-universe lifts align their total categories with stacks in groupoids, with
explicit upward and downward comparisons and induced morphisms between the lifted stacks.
-/

@[expose] public section

-- Local declaration justification (metaprogramming implementation): exposed data definitions
-- must reference their private projection laws under Lean's module visibility rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stack in sets `𝒮_X` associated to an algebraic space, obtained from its functor of
points as an fppf sheaf on `Sch/S`. -/
def stackInSets {S : Scheme.{u}} (X : AlgebraicSpace S) :
    StackOver.Sets (Scheme.fppfTopology.over S) :=
  (StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).obj
    (⟨X.functorOfPoints, X.isSheaf⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))

/-- The stack of points satisfies the site-level stack condition on the big fppf site. -/
instance instIsStackOnSite_stackInSets {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (stackInSets X).p :=
  IsStack.InSets.toOnSite inferInstance

namespace stackInSets

/-- The total functor on stacks of points induced by a morphism of algebraic spaces. -/
private def mapFunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (stackInSets X).total ⥤ (stackInSets Y).total :=
  StackOver.Sets.Hom.toFunctor
    ((StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).map (Sheaf.homEquiv.symm f))

/-- The functor induced by a morphism of algebraic spaces commutes with projection to schemes. -/
private theorem map_over {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    mapFunctor f ⋙ (stackInSets Y).p = (stackInSets X).p := sorry

/-- The cartesian `1`-morphism `𝒮_X ⟶ 𝒮_Y` induced by a morphism of algebraic spaces. -/
def map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CartesianBasedFunctor (stackInSets X).p (stackInSets Y).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (p := (stackInSets X).p) (q := (stackInSets Y).p)
      (mapFunctor f) (map_over (S := S) (X := X) (Y := Y) f))

/-- The identity morphism of an algebraic space induces the identity on its stack of points. -/
theorem map_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    map (𝟙 X) = CartesianBasedFunctor.id (stackInSets X).p := sorry

/-- A composite of morphisms of algebraic spaces induces the composite of their cartesian
morphisms on stacks of points. -/
theorem map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f).comp (map g) := sorry

end stackInSets

/-- The bundled two-universe lift of the total category of `𝒮_X`, matching the Hom-universe of
`[U/R]`. -/
def stackInSetsULiftTotal {S : Scheme.{u}} (X : AlgebraicSpace S) : Cat.{u + 1, u + 1} :=
  Cat.twoULift.{u + 1, u, u + 1, u + 1} (stackInSets X).total

/-- The two-universe lift of the projection of `𝒮_X`, landing in the Hom-universe of `[U/R]`. -/
def stackInSetsULiftProjection {S : Scheme.{u}} (X : AlgebraicSpace S) :
    stackInSetsULiftTotal X ⥤ Over S :=
  Cat.TwoULift.down.{u + 1, u, u + 1, u + 1} (stackInSets X).total ⋙ (stackInSets X).p

/-- The lifted projection of `𝒮_X` is a stack in groupoids on `(Sch/S)_fppf`. -/
instance instIsStackInGroupoids_stackInSetsULiftProjection {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (stackInSetsULiftProjection X) := sorry

/-- Universe-aligned presentation of `𝒮_X` in the bicategory containing `[U/R]`. -/
def stackInSetsULift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    StackOver.Groupoids.{u + 1, u, u + 1, u + 1} (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S)
    (stackInSetsULiftProjection X)
    (instIsStackInGroupoids_stackInSetsULiftProjection X)

namespace stackInSetsULift

/-- Forgetting the universe lift commutes with projection to the base scheme category. -/
private theorem down_over {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Cat.TwoULift.down.{u + 1, u, u + 1, u + 1} (stackInSets X).total ⋙
      (stackInSets X).p = (stackInSetsULift X).p := sorry

/-- The cartesian comparison forgetting the two-universe lift of `𝒮_X`. -/
def down {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CartesianBasedFunctor (stackInSetsULift X).p (stackInSets X).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor
      (Cat.TwoULift.down.{u + 1, u, u + 1, u + 1} (stackInSets X).total)
      (down_over X))

/-- Lifting the universe commutes with projection to the base scheme category. -/
private theorem up_over {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Cat.TwoULift.up.{u + 1, u, u + 1, u + 1} (stackInSets X).total ⋙
      (stackInSetsULift X).p = (stackInSets X).p := sorry

/-- The cartesian comparison `𝒮_X ⟶ 𝒮_X` lifting object and morphism universes. -/
def up {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CartesianBasedFunctor (stackInSets X).p (stackInSetsULift X).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor
      (Cat.TwoULift.up.{u + 1, u, u + 1, u + 1} (stackInSets X).total)
      (up_over X))

/-- The cartesian `1`-morphism `𝒮_X ⟶ 𝒮_Y` induced by a morphism of algebraic spaces, after
aligning both stacks to the Hom-universe of `[U/R]`. -/
def map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    stackInSetsULift X ⟶ stackInSetsULift Y :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (((stackInSetsULift.down X).comp (stackInSets.map f)).comp
          (stackInSetsULift.up Y)).toBasedFunctor)

end stackInSetsULift

end AlgebraicGeometry.AlgebraicSpace
