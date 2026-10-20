/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.5.3: Surjectivity of a morphism of algebraic spaces is equivalent
to scheme and affine base-change, étale atlas, and Zariski covering tests. -/
@[stacks 03MF] #check (AlgebraicGeometry.AlgebraicSpace.Surjective.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [Surjective f, Surjective.forallScheme f, Surjective.forallAffine f,
      Surjective.existsEtaleOnTarget f, Surjective.existsEtaleOnSource f,
      Surjective.existsEtaleSquare f, Surjective.existsZariskiCover f])

end AlgebraicGeometry.AlgebraicSpace
