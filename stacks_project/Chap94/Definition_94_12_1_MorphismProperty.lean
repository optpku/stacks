module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Smooth and surjective morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is smooth (resp. surjective) when every
representing morphism of algebraic spaces `Fy ⟶ ofOver U` is smooth
(resp. surjective).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.Smooth :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S},
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.Surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S},
    (X ⟶ Y) → Prop)

namespace Smooth

#check (AlgebraicGeometry.Groupoids.Hom.Smooth.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    Smooth (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.Smooth.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Smooth f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U},
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Smooth fy)

#check (AlgebraicGeometry.Groupoids.Hom.Smooth.relativelyRepresentable :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Smooth f],
    relativelyRepresentableByAlgebraicSpaces f)

end Smooth

namespace Surjective

#check (AlgebraicGeometry.Groupoids.Hom.Surjective.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    Surjective (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.Surjective.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Surjective f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U},
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Surjective fy)

#check (AlgebraicGeometry.Groupoids.Hom.Surjective.relativelyRepresentable :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Surjective f],
    relativelyRepresentableByAlgebraicSpaces f)

end Surjective

end AlgebraicGeometry.Groupoids.Hom
