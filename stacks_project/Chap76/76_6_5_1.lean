/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.NormalCone
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- 76.6.5.1: the canonical surjection of graded algebras
`Sym(C_{Z/X}) ⟶ C_{Z/X,*}` induces a closed immersion of cones over `Z`,
displayed as `C_{Z/X} ⟶ N_{Z/X}`. -/
@[stacks 09RV]
#check (AlgebraicGeometry.AlgebraicSpace.normalConeToNormalBundle i :
  normalCone i ⟶ normalBundle i)

#check (AlgebraicGeometry.AlgebraicSpace.relativeSpecMap_comp_π
  (ConormalAlgebra.symmetricToTotal i) :
  normalConeToNormalBundle i ≫ normalBundleπ i = normalConeπ i)

#check (AlgebraicGeometry.AlgebraicSpace.instIsClosedImmersion_normalConeToNormalBundle i :
  IsClosedImmersion (normalConeToNormalBundle i))
