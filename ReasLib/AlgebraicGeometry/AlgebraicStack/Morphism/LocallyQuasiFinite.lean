/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Locally quasi-finite neighbourhoods for morphisms to algebraic stacks

A locally finite-type morphism from an algebraic space to an algebraic stack
is locally quasi-finite on an open neighbourhood of the image of a
zero-dimensional point in a cartesian field fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A locally finite-type morphism from an algebraic space to an algebraic stack
is locally quasi-finite on an open subspace containing the image of any
zero-dimensional point of an algebraic-space model of a cartesian field fibre. -/
@[stacks 06ME]
theorem exists_openSubspace_locallyQuasiFinite_of_dimensionAt_eq_zero
    {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (p : FieldValuedPoint X) {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F)
    (hz : AlgebraicSpace.dimensionAt z = (0 : WithBot ℕ∞)) :
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
          (AlgebraicSpace.toGroupoids.map W.ι ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
