/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

/-!
# Induced field-valued points of algebraic stacks

Scheme points and field-valued points of algebraic spaces give field-valued
points of their associated algebraic stacks. Postcomposition sends scheme
points into the points of an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The field-valued point of the slice of `U` associated to a scheme point of `U`. -/
def FieldValuedPoint.ofResidue {S : Scheme.{u}} {U : Over S} (u : U.left) :
    FieldValuedPoint (GroupoidsOver.slice U) :=
  of (U.left.residueField u) (U.left.fromSpecResidueField u ≫ U.hom)
    (overMap (Over.homMk (U.left.fromSpecResidueField u)))

/-- The structure morphism of `ofResidue u` is the residue-field map of `u` over `S`. -/
theorem FieldValuedPoint.ofResidue_structureHom {S : Scheme.{u}} {U : Over S}
    (u : U.left) :
    (FieldValuedPoint.ofResidue u).structureHom =
      U.left.fromSpecResidueField u ≫ U.hom :=
  sorry

/-- The morphism of `ofResidue u` is `overMap` of the residue-field map of `u`. -/
theorem FieldValuedPoint.ofResidue_hom {S : Scheme.{u}} {U : Over S} (u : U.left) :
    (FieldValuedPoint.ofResidue u).hom =
      overMap (Over.homMk (U.left.fromSpecResidueField u)) :=
  sorry

/-- The field-valued point of `F.toGroupoids` associated to a field-valued point of an
algebraic space `F`. -/
def FieldValuedPoint.ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) : FieldValuedPoint F.toGroupoids :=
  of p.K p.structureHom
    ((AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫
      AlgebraicSpace.toGroupoids.map p.hom)

/-- `ofAlgebraicSpace` preserves the structure morphism to `S`. -/
theorem FieldValuedPoint.ofAlgebraicSpace_structureHom {S : Scheme.{u}}
    {F : AlgebraicSpace S} (p : AlgebraicSpace.FieldValuedPoint F) :
    (FieldValuedPoint.ofAlgebraicSpace p).structureHom = p.structureHom :=
  sorry

/-- The morphism of `ofAlgebraicSpace p` is the slice comparison followed by `toGroupoids.map`. -/
theorem FieldValuedPoint.ofAlgebraicSpace_hom {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    (FieldValuedPoint.ofAlgebraicSpace p).hom =
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫
        AlgebraicSpace.toGroupoids.map p.hom :=
  sorry

namespace Points

/-- The image in `|X|` of a scheme point of `U` along a morphism `slice U ⟶ X`. -/
def mapSlice {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) : Points X :=
  mk ((FieldValuedPoint.ofResidue u).map p)

/-- `mapSlice p u` is the class of the postcomposition of the residue-field point of `u`. -/
theorem mapSlice_mk {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) (u : U.left) :
    mapSlice p u = mk ((FieldValuedPoint.ofResidue u).map p) :=
  sorry

end Points

end AlgebraicGeometry.AlgebraicStack
