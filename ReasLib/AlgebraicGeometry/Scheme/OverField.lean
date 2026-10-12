/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Over

/-!
# Schemes and algebras over a field

This leaf provides the common slice-category spelling for schemes over the
spectrum of a field and the corresponding category of commutative algebras.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme over the field `k`, packaged canonically as an object of `Over (Spec k)`. -/
@[stacks 06LH]
abbrev SchemeOverField (k : Type u) [Field k] :=
  Over (Spec (CommRingCat.of k))

/-- A commutative `k`-algebra, packaged canonically as an object of `CommAlgCat k`. -/
@[stacks 06LH]
abbrev CommAlgOverField (k : Type u) [Field k] :=
  CommAlgCat.{u} k

end AlgebraicGeometry
