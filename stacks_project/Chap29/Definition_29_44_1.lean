/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/- Definition 29.44.1 (1): a morphism of schemes `f : X ⟶ S` is integral when it is affine and
the induced map on sections over every affine open of `S` is integral. -/
@[stacks 01WH] #check (AlgebraicGeometry.IsIntegralHom f : Prop)

/- The canonical integral-morphism predicate has the stated affine-open characterization. -/
#check (AlgebraicGeometry.isIntegralHom_iff f :
  AlgebraicGeometry.IsIntegralHom f ↔
    AlgebraicGeometry.IsAffineHom f ∧
      ∀ U : S.Opens, AlgebraicGeometry.IsAffineOpen U → (f.app U).hom.IsIntegral)

/- Definition 29.44.1 (2): a morphism of schemes `f : X ⟶ S` is finite when it is affine and
the induced map on sections over every affine open of `S` is finite. -/
@[stacks 01WH] #check (AlgebraicGeometry.IsFinite f : Prop)

/- The canonical finite-morphism predicate has the stated affine-open characterization. -/
#check (AlgebraicGeometry.isFinite_iff f :
  AlgebraicGeometry.IsFinite f ↔
    AlgebraicGeometry.IsAffineHom f ∧
      ∀ U : S.Opens, AlgebraicGeometry.IsAffineOpen U → (f.app U).hom.Finite)
