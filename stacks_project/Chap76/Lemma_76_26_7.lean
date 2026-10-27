/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay.Locus

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.26.7 (1): the Cohen--Macaulay locus of a flat, locally finitely
presented morphism of algebraic spaces is open. -/
@[stacks 0E10]
#check (AlgebraicGeometry.AlgebraicSpace.isOpen_cohenMacaulayLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f],
    IsOpen (cohenMacaulayLocus f))

/- Lemma 76.26.7 (2): the Cohen--Macaulay locus of a flat, locally finitely
presented morphism of algebraic spaces commutes with arbitrary base change. -/
@[stacks 0E10]
#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulayLocus_eq_preimage_of_isPullback :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f],
    cohenMacaulayLocus f' = Points.map g' ⁻¹' cohenMacaulayLocus f)

end AlgebraicGeometry.AlgebraicSpace
