/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Cohomology

/-!
# Stage pullbacks and spaces-étale cohomology

Typed checks of the shared stage pullback, étale cohomology, and first-page
coefficient functors.
-/

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Functor
open scoped Simplicial

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.pullbackStage :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    {U : SimplicialObject (AlgebraicSpace S)} →
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) → (n : ℕ) →
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (spacesEtaleTopology (U.obj (op ⦋n⦌))) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusCohomology :
  {S : Scheme.{u}} → (Y : AlgebraicSpace S) → (n : ℤ) →
    Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.pageOneFunctorNonneg :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    {U : SimplicialObject (AlgebraicSpace S)} →
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) → (n : ℕ) → (q : ℤ) →
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
