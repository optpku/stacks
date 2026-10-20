module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Big

/-!
# Big fppf sheaf functors on algebraic spaces

A morphism of algebraic spaces induces a morphism of big fppf topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

universe u

/-- A morphism of algebraic spaces induces a morphism of big fppf topoi. -/
noncomputable abbrev AlgebraicGeometry.AlgebraicSpace.Fppf.Big.morphismOfTopoi
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      ((fppfTopology S).over X) ((fppfTopology S).over Y) :=
  CategoryTheory.Over.Site.morphismOfTopoi (fppfTopology S) f

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.Big.morphismOfTopoi :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      ((fppfTopology S).over X) ((fppfTopology S).over Y))
