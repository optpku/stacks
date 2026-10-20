/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.3.2: For a quasi-compact quasi-separated morphism and a quasi-coherent module,
cohomology on an affine étale pullback agrees with degree-zero cohomology of its higher
direct image for every integer degree. -/
@[stacks 08EX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.cohomology_iso_higherDirectImage_degreeZero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
      (F : X.Modules) [F.IsQuasicoherent]
      (V : smallEtaleSite Y) [AlgebraicGeometry.IsAffine V.left.left] (q : ℤ)
      [HasSheafify (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology (Limits.pullback V.hom f)) AddCommGrpCat.{u})]
      [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})],
      IsIsomorphic (cohomologyOnEtalePullback f F V q)
        (higherDirectImage_degreeZero_cohomology f F V q))
