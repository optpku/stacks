/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.40.2: Properness is equivalent to the scheme-valued, affine,
surjective étale atlas, and Zariski-covering tests. -/
@[stacks 083R] #check (AlgebraicGeometry.AlgebraicSpace.Proper.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [Proper f, Proper.forallScheme f, Proper.forallAffine f,
      Proper.existsEtaleOnTarget f, Proper.existsZariskiCover f])

end AlgebraicGeometry.AlgebraicSpace
