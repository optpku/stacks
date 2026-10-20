/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.Locality

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.19.6: Universal injectivity is equivalent to its scheme, affine,
surjective-scheme, and Zariski-local pullback tests. -/
@[stacks 03MX] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [UniversallyInjective f, UniversallyInjective.forallScheme f,
      UniversallyInjective.forallAffine f,
      UniversallyInjective.existsSchemeSurjectiveOnTarget f,
      UniversallyInjective.existsZariskiCover f])

end AlgebraicGeometry.AlgebraicSpace
