/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.FlatRestriction
import StacksCheckRecall

/-!
# Restriction of the quasi-coherent adjunction counit along a flat object

On an algebraic stack, the counit `Q(F) ⟶ F` of the adjunction
`QCoh.toLQCohFbc ⊣ LQCohFbc.toQCoh` becomes an isomorphism after restriction
to the small étale site of a flat scheme object.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids

universe u

/- Lemma 103.10.4: on an algebraic stack `X`, if `x` is an object over a
scheme `U` such that `x : U ⟶ X` is flat, then for `F` in `LQCohFbc X` the
restricted counit `Q(F)|_{U_étale} ⟶ F|_{U_étale}` is an isomorphism. -/
@[stacks 0GQK] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_counit_restrictToSmallEtale_isIso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
      (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
      (F : LQCohFbc X), IsIso (LQCohFbc.toQCoh_counit_restrictToSmallEtale x F))

