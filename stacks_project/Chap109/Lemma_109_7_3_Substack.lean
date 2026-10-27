/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import stacks_project.Chap108.Lemma_108_4_5_OpenImmersion

/-! # The object property of Deligne–Mumford families of curves

Typed compatibility checks for full subcategories and the open DM locus.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.ofObjectProperty :
  ∀ {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)],
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.inclusionOf :
  ∀ {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [Functor.IsFibered.InGroupoids (Q.ι ⋙ p S)],
    ofObjectProperty Q ⟶ toGroupoids S)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.dm_iff :
  ∀ {S : Scheme.{u}} (P : Obj S), dm S P ↔ IsUnramified P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsOpenDMSubstack_dm :
  ∀ (S : Scheme.{u}), IsOpenDMSubstack (dm S))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
