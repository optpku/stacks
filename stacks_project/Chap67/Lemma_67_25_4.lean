/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
import StacksCheckRecall

/-!
# Images of finite type points under locally finite type morphisms

A locally-of-finite-type morphism of algebraic spaces sends finite-type points
to finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.25.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type, then
`Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y`. -/
@[stacks 06EI] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.image_finiteTypePoints_subset :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f],
      Points.map f '' finiteTypePoints X ⊆ finiteTypePoints Y)

/- A locally-of-finite-type morphism of algebraic spaces sends finite-type
points to finite-type points. -/
#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.map_mem_finiteTypePoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f] {x : Points X},
    x ∈ finiteTypePoints X → Points.map f x ∈ finiteTypePoints Y)
