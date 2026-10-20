/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalLifts.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

/- Lemma 106.7.2. For an algebraic stack with locally finitely presented inertia,
isomorphism classes of infinitesimal lifts form a sheaf on the big affine fppf
site of the thickened base. -/
@[stacks 0DNS] #check (AlgebraicGeometry.GroupoidsOver.infinitesimalLiftPresheaf_isSheaf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)]
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA)),
    Presheaf.IsSheaf (Scheme.bigAffineFppfTopology (Spec A'))
      (infinitesimalLiftPresheaf fA hfA x))
