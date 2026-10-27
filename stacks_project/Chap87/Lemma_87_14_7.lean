/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.CountablyIndexedCompletion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.GabberCompletion
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 87.14.7 (1): A countably indexed affine completion along a closed
subset cut out by countably many functions is adic*. -/
@[stacks 0APW] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isAdicStarAffine_of_countablyIndexedAlong :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
      (structureHom : Spec (.of A) ⟶ S) (T : Closeds (Spec (.of A)))
      [AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine
        (AlgebraicGeometry.AffineFormalAlgebraicSpace.affineCompletionAlong structureHom T)],
      AlgebraicGeometry.AffineFormalAlgebraicSpace.cutOutByCountable T →
        AlgebraicGeometry.FormalAlgebraicSpace.IsAdicStarAffine
          (AlgebraicGeometry.AffineFormalAlgebraicSpace.affineCompletionAlong structureHom T))

/- Lemma 87.14.7 (2): Gabber's countably indexed affine completion is not
adic*, so countable cutting-out is necessary in the first clause. -/
@[stacks 0APW] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.gabber_not_isAdicStarAffine :
    ∀ (k : Type u) [Field k],
      ¬ AlgebraicGeometry.FormalAlgebraicSpace.IsAdicStarAffine
        (AlgebraicGeometry.AffineFormalAlgebraicSpace.affineCompletionAlong
          (AlgebraicGeometry.AffineFormalAlgebraicSpace.counterexample.structureHom k)
          (AlgebraicGeometry.AffineFormalAlgebraicSpace.counterexample.zeroLocus k)))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.gabber_isCountablyIndexedAffine :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine
      (AlgebraicGeometry.AffineFormalAlgebraicSpace.affineCompletionAlong
        (AlgebraicGeometry.AffineFormalAlgebraicSpace.counterexample.structureHom k)
        (AlgebraicGeometry.AffineFormalAlgebraicSpace.counterexample.zeroLocus k)))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.not_cutOutByCountable_gabber :
  ∀ (k : Type u) [Field k],
    ¬ AlgebraicGeometry.AffineFormalAlgebraicSpace.cutOutByCountable
      (AlgebraicGeometry.AffineFormalAlgebraicSpace.counterexample.zeroLocus k))
