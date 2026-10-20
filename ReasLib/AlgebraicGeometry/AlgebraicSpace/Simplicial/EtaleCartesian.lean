/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleAugmentation
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Cartesian sheaves on simplicial étale sites -/

set_option backward.privateInPublic true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.SimplicialSites AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesian

/-- The inverse-image transition is the adjunction mate of the pushforward transition. -/
private noncomputable def inverseTransition
    {C : SimplexCategory → Type (u + 1)} [∀ n, Category.{u + 1} (C n)]
    {J : ∀ n, GrothendieckTopology (C n)}
    {fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → MorphismOfTopoiIn (J m) (J n)}
    {h : HasPushforwardFunctoriality J fHom}
    (F : @SheafSystem.Obj _ _ J fHom h) {m n : SimplexCategory} (φ : m ⟶ n) :=
  @SheafSystem.mapInverseImage _ _ _ _ h F m n φ

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- A total étale sheaf is cartesian when every stage inverse-image transition is invertible. -/
def IsCartesian (G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) : Prop :=
  ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (inverseTransition ((toEtaleSheafSystem U).obj G) φ)

/-- Cartesianness is equivalent to invertibility of all canonical inverse-image transitions. -/
theorem isCartesian_iff (G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    IsCartesian U G ↔ ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      IsIso (inverseTransition ((toEtaleSheafSystem U).obj G) φ) := Iff.rfl

/-- An abelian total étale sheaf is cartesian when its underlying sheaf of sets is cartesian. -/
def IsCartesianAbelian (G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) : Prop :=
  IsCartesian U ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).obj G)

/-- Abelian cartesianness is cartesianness after forgetting the group operations. -/
theorem isCartesianAbelian_iff
    (G : Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :
    IsCartesianAbelian U G ↔
      IsCartesian U ((sheafCompose _ (forget AddCommGrpCat.{u + 1})).obj G) := Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleCartesian
