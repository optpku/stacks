/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local

/-! # Étale neighbourhoods detected on field fibres -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Let `X` be an algebraic stack. Consider a cartesian diagram
where `U` is an algebraic space, `k` is a field, and `U ⟶ X` is flat and
locally of finite presentation. Let `z` be a point of an algebraic-space model
`F` of the cartesian field fibre `U ×_X Spec(k)` such that `F ⟶ Spec(k)` is
unramified at `z`. Then after replacing `U` by an open subspace containing the
image of `z` in `|U|`, the morphism `U ⟶ X` is étale. -/
@[stacks 06N2]
theorem exists_openSubspace_etale {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint X)
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F)
    (h_unramified : AlgebraicSpace.UnramifiedAt (representedFiberToSpec e) z) :
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Etale (openSubspaceToStack f W) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
