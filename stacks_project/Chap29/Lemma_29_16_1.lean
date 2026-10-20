/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.16.1: For a field-valued point, finite type, local finite type, existence of an
affine-open factorization with finite coordinate-ring map, and existence of an affine-open
factorization through a closed point with finite residue-field extension are equivalent. -/
@[stacks 01TA] #check
  (AlgebraicGeometry.Scheme.Hom.FieldValuedPoint.finiteType_tfae :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
      (f : Spec (CommRingCat.of k) ⟶ S),
      List.TFAE [
        AlgebraicGeometry.Scheme.Hom.FiniteType f,
        AlgebraicGeometry.LocallyOfFiniteType f,
        AlgebraicGeometry.Scheme.Hom.FieldValuedPoint.HasFiniteCoordinateRingMapOnAffineOpen f,
        AlgebraicGeometry.Scheme.Hom.FieldValuedPoint.HasClosedImageWithFiniteResidueExtensionOnAffineOpen f])
