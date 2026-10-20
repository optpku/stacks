/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.Neighborhood
import StacksCheckRecall

/-!
# Shrinking a flat locally finitely presented morphism to an étale morphism

An unramified point of a cartesian field fibre of a flat, locally finitely
presented morphism from an algebraic space to an algebraic stack lies in an
open subspace on which the restricted morphism is étale.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.21.5: An unramified point of a cartesian field fibre of a flat,
locally finitely presented morphism has image in an open subspace on which
the morphism is étale. -/
@[stacks 06N2] #check (AlgebraicGeometry.AlgebraicStack.exists_openSubspace_etale :
    ∀ {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint X)
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F)
    (h_unramified : AlgebraicSpace.UnramifiedAt (representedFiberToSpec e) z),
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Etale (openSubspaceToStack f W))

end AlgebraicGeometry.AlgebraicStack
