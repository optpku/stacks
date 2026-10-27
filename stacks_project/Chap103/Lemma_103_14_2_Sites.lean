/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Precoverage

/-! Compatibility checks for the inclusion properties of Lemma 103.14.2. -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
universe u z
namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}}

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion.instIsContinuous :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    (lisseEtaleInclusion X).IsContinuous (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion.instIsCocontinuous :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    (lisseEtaleInclusion X).IsCocontinuous (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion.instIsContinuous :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    (flatFppfInclusion X).IsContinuous (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion.instIsCocontinuous :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    (flatFppfInclusion X).IsCocontinuous (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion.instPrecoverageIsContinuous :
  ∀
    (X : GroupoidsOver S) [AlgebraicStack X],
    Functor.Precoverage.IsContinuous (lisseEtaleInclusion X)
      (lisseEtalePrecoverage X) X.etaleTopology.toPrecoverage)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion.instPrecoverageIsCocontinuous :
  ∀
    (X : GroupoidsOver S) [AlgebraicStack X],
    Functor.Precoverage.IsCocontinuous (lisseEtaleInclusion X)
      (lisseEtalePrecoverage X) X.etaleTopology.toPrecoverage)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion.instPrecoverageIsContinuous :
  ∀
    (X : GroupoidsOver S) [AlgebraicStack X],
    Functor.Precoverage.IsContinuous (flatFppfInclusion X)
      (flatFppfPrecoverage X) (inheritedFppfTopology X).toPrecoverage)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion.instPrecoverageIsCocontinuous :
  ∀
    (X : GroupoidsOver S) [AlgebraicStack X],
    Functor.Precoverage.IsCocontinuous (flatFppfInclusion X)
      (flatFppfPrecoverage X) (inheritedFppfTopology X).toPrecoverage)

#check (AlgebraicGeometry.AlgebraicStack.etaleTopology_hasWeakSheafify :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}],
    HasWeakSheafify X.etaleTopology AddCommGrpCat.{z})

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleTopology_hasWeakSheafify_of_univLE :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}],
    HasWeakSheafify (lisseEtaleTopology X) AddCommGrpCat.{z})

#check (AlgebraicGeometry.AlgebraicStack.inheritedFppfTopology_hasWeakSheafify :
  ∀ (X : GroupoidsOver S) [UnivLE.{u + 1, z}],
    HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{z})

#check (AlgebraicGeometry.AlgebraicStack.flatFppfTopology_hasWeakSheafify_of_univLE :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}],
    HasWeakSheafify (flatFppfTopology X) AddCommGrpCat.{z})

end AlgebraicGeometry.AlgebraicStack
