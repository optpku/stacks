module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap69.Lemma_69_19_1_DVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Separated
import StacksCheckRecall

/-!
# Lemma 69.19.1

A locally of finite type quasi-separated morphism of algebraic spaces into a
locally Noetherian algebraic space is separated as soon as every DVR valuative
square has at most one lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.19.1: If `f : X ⟶ Y` is a morphism of algebraic spaces over a scheme
`S`, `Y` is locally Noetherian, `f` is locally of finite type and quasi-separated,
and every DVR valuative square has at most one lift, then `f` is separated. -/
@[stacks 0ARJ] #check (AlgebraicGeometry.AlgebraicSpace.Separated.of_dvrUniqueness :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
    [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness f],
    AlgebraicGeometry.AlgebraicSpace.Separated f)
