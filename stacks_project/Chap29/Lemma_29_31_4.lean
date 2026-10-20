/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
import StacksCheckRecall

open CategoryTheory Limits

universe u

variable {Z X Z' X' : AlgebraicGeometry.Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.IsImmersion i']
variable (sq : IsPullback f i i' g)

/- Lemma 29.31.4: for a cartesian square of scheme immersions, the canonical conormal comparison
is an epimorphism; it is an isomorphism when the ambient morphism is flat. -/
@[stacks 0473] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.map_epi_of_isPullback sq :
    Epi (AlgebraicGeometry.Scheme.Hom.Conormal.map sq.toCommSq))

variable [AlgebraicGeometry.Flat g]

/- Under flat base change, the same canonical conormal comparison is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.map_isIso_of_isPullback_of_flat sq :
    IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.map sq.toCommSq))
