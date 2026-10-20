module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Flat morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is flat when every representing morphism of
algebraic spaces `Fy ⟶ ofOver U` is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.Flat :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

namespace Flat

#check (AlgebraicGeometry.Groupoids.Hom.Flat.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}, Flat (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.Flat.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Flat f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U},
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Flat fy)

#check (AlgebraicGeometry.Groupoids.Hom.Flat.relativelyRepresentable :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Flat f],
    relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.Groupoids.Hom.Flat.iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    Flat f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → AlgebraicSpace.Flat fy)

end Flat

end AlgebraicGeometry.Groupoids.Hom
