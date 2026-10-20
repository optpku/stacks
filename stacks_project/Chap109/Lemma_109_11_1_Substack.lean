/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReducedConnected
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap75.Lemma_75_26_8_GeometricFibres
public import stacks_project.Chap109.Lemma_109_10_1_Substack

/-!
# The object property of geometrically reduced connected curves of dimension 1

`𝒞urves^{grc, 1}` is the full subcategory of families of curves whose
geometric fibres are reduced, connected, and of dimension `1`. Membership is
the source-facing packaging of a classifying morphism factoring through that
open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1 :
    ∀ (S : Scheme.{u}), ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      geometricallyReducedConnectedDim1 S P ↔
        Hom.HasReducedGeometricFibres (hom P) ∧
          AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (hom P) ∧
            ∀ ybar : GeometricPoint (ofOver (base P)),
              dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_geometricallyReducedConnectedDim1 :
    ∀ (S : Scheme.{u}), (geometricallyReducedConnectedDim1 S).IsClosedUnderIsomorphisms)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
