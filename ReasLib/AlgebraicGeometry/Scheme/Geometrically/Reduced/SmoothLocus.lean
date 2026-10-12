/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Smooth loci of geometrically reduced schemes

This file records the dense-open smoothness criterion for geometrically reduced schemes
locally of finite type over a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A reduced scheme locally of finite type over a field is geometrically reduced exactly when
it contains a dense open subscheme that is smooth over the field. -/
@[stacks 056V]
theorem geometricallyReduced_iff_exists_dense_open_smooth
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] [IsReduced X.left] :
    geometricallyReduced X ↔
      ∃ U : X.left.Opens, Dense (U : Set X.left) ∧ Smooth (U.ι ≫ X.hom) := sorry

/-- A variety over a field is geometrically reduced exactly when it contains a nonempty open
subscheme that is smooth over the field. -/
theorem geometricallyReduced_iff_exists_nonempty_open_smooth
    (X : SchemeOverField k) [Variety X] :
    geometricallyReduced X ↔
      ∃ U : X.left.Opens, U ≠ ⊥ ∧ Smooth (U.ι ≫ X.hom) := sorry

end AlgebraicGeometry.SchemeOverField
