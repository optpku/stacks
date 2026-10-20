module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Representable morphisms of groupoid fibrations having a morphism property

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` has a
property `P` of morphisms of algebraic spaces when every scheme-slice
representing morphism has `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.has :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S},
    MorphismProperty (AlgebraicSpace S) → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.has_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : X ⟶ Y),
    AlgebraicGeometry.Groupoids.Hom.has P f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → P fy)

#check (AlgebraicGeometry.Groupoids.Hom.has.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (hf : AlgebraicGeometry.Groupoids.Hom.has P f)
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy),
    P fy)

#check (AlgebraicGeometry.Groupoids.Hom.has.of :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {P : MorphismProperty (AlgebraicSpace S)} {f : X ⟶ Y}
    (h : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ AlgebraicSpace.ofOver U),
      RepresentsBaseChange f y Fy fy → P fy),
    AlgebraicGeometry.Groupoids.Hom.has P f)
