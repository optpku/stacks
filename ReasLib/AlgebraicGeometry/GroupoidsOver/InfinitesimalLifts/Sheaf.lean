/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import ReasLib.RingTheory.RingHom.SquareZero
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalLifts.Presheaf

/-!
# Sheaf of infinitesimal lifts

On an algebraic stack whose inertia morphism is locally of finite presentation,
isomorphism classes of infinitesimal lifts of a square-zero deformation form a
sheaf on the big affine fppf site of the thickened base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For an algebraic stack with locally finitely presented inertia, the
presheaf of isomorphism classes of lifts of a fibre object across a square-zero
extension is a sheaf on the big affine fppf site of the thickened base. -/
theorem infinitesimalLiftPresheaf_isSheaf {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA)) :
    Presheaf.IsSheaf (Scheme.bigAffineFppfTopology (Spec A'))
      (infinitesimalLiftPresheaf fA hfA x) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
