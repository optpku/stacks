/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

The constructions retain their original public names and concrete data.
Existing proposition-valued laws remain explicit proof obligations.
-/

@[expose] public section

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

/-- The cartesian `1`-morphism `𝒮_X ⟶ 𝒮_Y` induced by a morphism of algebraic spaces. -/
def stackInSets.map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CartesianBasedFunctor (stackInSets X).p (stackInSets Y).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor
      (StackOver.Sets.Hom.toFunctor
        ((StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).map (Sheaf.homEquiv.symm f)))
      sorry)

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

/-- The cartesian comparison forgetting the two-universe lift of `𝒮_X`. -/
def stackInSetsULift.down {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CartesianBasedFunctor (stackInSetsULift X).p (stackInSets X).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor
      (Cat.TwoULift.down.{u + 1, u, u + 1, u + 1} (stackInSets X).total) sorry)

/-- The cartesian comparison `𝒮_X ⟶ 𝒮_X` lifting object and morphism universes. -/
def stackInSetsULift.up {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CartesianBasedFunctor (stackInSets X).p (stackInSetsULift X).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor
      (Cat.TwoULift.up.{u + 1, u, u + 1, u + 1} (stackInSets X).total) sorry)

/-- The cartesian `1`-morphism `𝒮_X ⟶ 𝒮_Y` induced by a morphism of algebraic spaces, after
aligning both stacks to the Hom-universe of `[U/R]`. -/
def stackInSetsULift.map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    stackInSetsULift X ⟶ stackInSetsULift Y :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (((stackInSetsULift.down X).comp (stackInSets.map f)).comp
          (stackInSetsULift.up Y)).toBasedFunctor)

end AlgebraicGeometry.AlgebraicSpace
