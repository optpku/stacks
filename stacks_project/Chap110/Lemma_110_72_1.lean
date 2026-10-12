/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import stacks_project.Chap110.Lemma_110_52_1_Torsors
public import stacks_project.Chap110.Lemma_110_72_1_AbelianScheme
public import stacks_project.Chap110.Lemma_110_72_3_Cohomology

/-!
# Fppf H¹ of an abelian scheme over a surface injects into the generic fibre
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.GroupScheme

/-- Commutativity of a group scheme passes to the associated group algebraic space. -/
instance instIsCommMonObj_toGroupAlgebraicSpace {S : Scheme.{u}} (G : GroupScheme S)
    [IsCommMonObj G.X] : IsCommMonObj (toGroupAlgebraicSpace G).X :=
  sorry

/-- Restriction of fppf H¹ of a commutative group scheme from `W` to
`Spec W.functionField`, as the `cohomologyPresheaf` map along
`Over.homMk (W.fromSpecStalk (genericPoint W))`. -/
def fppfH1RestrictFunctionField {W : Scheme.{u}} [IsIntegral W] (G : GroupScheme W)
    [IsCommMonObj G.X]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u})] :
    (additiveFppfSheaf (toGroupAlgebraicSpace G)
        (𝟙 (ofOver (Over.mk (𝟙 W))))).H' 1 (Over.mk (𝟙 W)) ⟶
      (additiveFppfSheaf (toGroupAlgebraicSpace G)
        (𝟙 (ofOver (Over.mk (𝟙 W))))).H' 1
        (Over.mk (W.fromSpecStalk (genericPoint W))) :=
  ((additiveFppfSheaf (toGroupAlgebraicSpace G)
      (𝟙 (ofOver (Over.mk (𝟙 W))))).cohomologyPresheaf 1).map
    (Over.homMk (W.fromSpecStalk (genericPoint W))).op

/-- Unfolding `fppfH1RestrictFunctionField` recovers restriction of
`cohomologyPresheaf` along `W.fromSpecStalk (genericPoint W)`. -/
theorem fppfH1RestrictFunctionField_def {W : Scheme.{u}} [IsIntegral W]
    (G : GroupScheme W) [IsCommMonObj G.X]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u})] :
    fppfH1RestrictFunctionField G =
      ((additiveFppfSheaf (toGroupAlgebraicSpace G)
          (𝟙 (ofOver (Over.mk (𝟙 W))))).cohomologyPresheaf 1).map
        (Over.homMk (W.fromSpecStalk (genericPoint W))).op :=
  sorry

/-- Lemma 110.72.1: If `W` is a two-dimensional regular integral Noetherian scheme
and `G` is an abelian scheme over `W`, then the restriction map
`fppfH1RestrictFunctionField G` from fppf H¹ of `G` over `W` to fppf H¹ of `G`
over `Spec W.functionField` is injective. -/
@[stacks 0AF9]
theorem fppfH1RestrictFunctionField_injective {W : Scheme.{u}}
    [IsIntegral W] [IsNoetherian W] [Scheme.Regular W]
    (hdim : topologicalKrullDim W = 2) (G : GroupScheme W) [AbelianScheme G]
    [HasSheafify (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Over.mk (𝟙 W)).left) AddCommGrpCat.{u})] :
    Function.Injective (fppfH1RestrictFunctionField G).hom :=
  sorry

end AlgebraicGeometry.GroupScheme

