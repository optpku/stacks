/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Cohomology
public import ReasLib.AlgebraicGeometry.GroupScheme.AlgebraicSpace
import StacksCheckRecall

/-!
# Fppf H¹ of an abelian scheme over a surface injects into the generic fibre
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

/- Lemma 110.72.1: For an abelian scheme over a two-dimensional regular integral
Noetherian scheme, restriction of first fppf cohomology to the function field
is injective. -/
@[stacks 0AF9] #check
  (AlgebraicGeometry.GroupScheme.fppfH1RestrictFunctionField_injective :
    ∀ {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W] [Scheme.Regular W],
      topologicalKrullDim W = 2 →
      ∀ (G : GroupScheme W) [GroupScheme.AbelianScheme G]
        [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
        [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left)
          AddCommGrpCat.{u})],
        Function.Injective (GroupScheme.fppfH1RestrictFunctionField G).hom)
