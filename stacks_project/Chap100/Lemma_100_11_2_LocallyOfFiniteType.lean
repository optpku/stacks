/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType

/-!
# Locally of finite type morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is locally of finite type when every
representing morphism of algebraic spaces `Fy ⟶ ofOver U` is locally of finite
type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    Prop)

namespace LocallyOfFiniteType

#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    LocallyOfFiniteType (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy),
    AlgebraicSpace.LocallyOfFiniteType fy)

#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LocallyOfFiniteType f],
    relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    LocallyOfFiniteType f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFiniteType fy)

end LocallyOfFiniteType

end AlgebraicGeometry.Groupoids.Hom
