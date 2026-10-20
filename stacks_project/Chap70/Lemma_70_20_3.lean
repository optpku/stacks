/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.FinitePresentation
import StacksCheckRecall

/-!
# Testing properness of separated finite-type morphisms of algebraic spaces

Lemma 70.20.3 records that a separated finite-type morphism of algebraic spaces
is proper iff this is tested by closed projections after base change locally of
finite presentation, and iff some surjective étale scheme atlas of the target
has closed affine-space product projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.20.3: a separated finite-type morphism is proper iff every base
change along a locally finitely presented morphism Z ⟶ Y is closed, and iff
all affine-space product projections are closed after passage to some
surjective étale scheme atlas of Y. -/
@[stacks 0CMA] #check (AlgebraicGeometry.AlgebraicSpace.Proper.tfae_separatedFiniteType :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] [FiniteType f],
    List.TFAE [Proper f, Closed.forallLocallyOfFinitePresentation f,
      Closed.existsEtaleAffineSpace f])

#check (AlgebraicGeometry.AlgebraicSpace.Proper.iff_forallLocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] [FiniteType f],
    Proper f ↔ Closed.forallLocallyOfFinitePresentation f)

#check (AlgebraicGeometry.AlgebraicSpace.Proper.iff_existsEtaleAffineSpace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] [FiniteType f],
    Proper f ↔ Closed.existsEtaleAffineSpace f)
