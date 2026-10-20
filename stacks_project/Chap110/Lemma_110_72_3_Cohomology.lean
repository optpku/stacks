/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.CategoryTheory.Monoidal.Mon
public import stacks_project.Chap78.Lemma_78_5_2_Over
public import stacks_project.Chap95.Lemma_95_14_10_SheafTorsors

/-!
# Additive fppf sheaf of a commutative group algebraic space

Scheme-valued points of a commutative group algebraic space, rewritten additively,
form an abelian sheaf on the big fppf site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- Fibre points of a commutative group algebraic space form a commutative group. -/
instance instCommGroup_fiberPoint [IsCommMonObj G.X] {U : Over S} (b : ofOver U ⟶ B)
    (V : Over U.left) : CommGroup (FiberPoint G b V) :=
  { instGroup_fiberPoint G b V with mul_comm := sorry }

end AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors

namespace AlgebraicGeometry.GroupAlgebraicSpace

open SheafTorsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- The additive fppf sheaf of points of `U ×_{b,B} G` on `(Sch/U)_fppf`. -/
def additiveFppfSheaf [IsCommMonObj G.X] {U : Over S} (b : ofOver U ⟶ B) :
    Sheaf (Scheme.fppfTopology.over U.left) AddCommGrpCat.{u} where
  obj :=
    { obj V := AddCommGrpCat.of (Additive (FiberPoint G b V.unop))
      map f := AddCommGrpCat.ofHom (FiberPoint.resHom G f.unop).toAdditive
      map_id := sorry
      map_comp := sorry }
  property := sorry

/-- Sections of `additiveFppfSheaf G b` over `V` are the additive group of fibre points. -/
theorem additiveFppfSheaf_obj [IsCommMonObj G.X] {U : Over S} (b : ofOver U ⟶ B)
    (V : (Over U.left)ᵒᵖ) :
    (additiveFppfSheaf G b).obj.obj V =
      AddCommGrpCat.of (Additive (FiberPoint G b V.unop)) := sorry

/-- Restriction maps of `additiveFppfSheaf G b` are the additive form of `FiberPoint.resHom`. -/
theorem additiveFppfSheaf_map [IsCommMonObj G.X] {U : Over S} (b : ofOver U ⟶ B)
    {V W : (Over U.left)ᵒᵖ} (f : V ⟶ W) :
    (additiveFppfSheaf G b).obj.map f =
      AddCommGrpCat.ofHom (FiberPoint.resHom G f.unop).toAdditive := sorry

end AlgebraicGeometry.GroupAlgebraicSpace

