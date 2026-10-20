module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty

/-!
# Étale morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is étale when every representing morphism of
algebraic spaces `Fy ⟶ ofOver U` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.Etale :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

namespace Etale

#check (AlgebraicGeometry.Groupoids.Hom.Etale.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    Etale (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.Etale.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Etale f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy),
    AlgebraicSpace.Etale fy)

#check (AlgebraicGeometry.Groupoids.Hom.Etale.relativelyRepresentable :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Etale f],
    relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.Groupoids.Hom.Etale.smooth_of_etale :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Etale f],
    Smooth f)

end Etale

end AlgebraicGeometry.Groupoids.Hom
