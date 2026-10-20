/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Locality
import StacksCheckRecall

/-!
# Characterizations of finite locally free morphisms of algebraic spaces

Lemma 67.46.3 records that a morphism of algebraic spaces is finite locally
free iff it is representable and finite locally free, iff some surjective étale
scheme atlas has finite locally free projection, and iff some Zariski covering
of the target has finite locally free inverse images.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.46.3: for a morphism of algebraic spaces over a scheme, representable
finite local freeness, finite local freeness, finite local freeness after a
surjective étale scheme atlas of the target, and finite local freeness on a
Zariski covering of the target are equivalent. -/
@[stacks 03ZW] #check (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.representable f,
      AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree f,
      AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.existsSurjectiveEtaleTarget f,
      AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.existsZariskiCover f])
