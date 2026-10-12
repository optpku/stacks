/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of commutative algebras

Forgetting a commutative algebra to its underlying commutative ring preserves limits.  The
universe-polymorphic instance here is the low-level owner used by algebra-valued sheaves; it does
not depend on any site or sheaf construction.
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

variable {R : Type u} [CommRing R]

/-- The category of commutative algebras has limits when its universe bounds the indexing
category's object universe. -/
theorem hasLimitsOfSize_of_univLE [UnivLE.{v, w}] :
    HasLimitsOfSize.{t, v} (CommAlgCat.{w} R) := sorry

/-- The category of commutative `R`-algebras has limits indexed by every category whose object
universe is bounded by the algebra universe.  The lower priority leaves mathlib's same-universe
instance canonical when both apply. -/
@[stacks 0CS6 "limits of commutative algebras"]
instance (priority := 90) hasLimitsOfSize [UnivLE.{v, w}] :
    HasLimitsOfSize.{t, v} (CommAlgCat.{w} R) :=
  hasLimitsOfSize_of_univLE

/-- The forgetful functor from commutative algebras to commutative rings preserves limits when
the algebra universe bounds the indexing category's object universe. -/
theorem forgetToCommRing_preservesLimitsOfSize_of_univLE [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (CommAlgCat.{w} R) CommRingCat.{w}) := sorry

/-- The forgetful functor from commutative `R`-algebras to commutative rings preserves limits of
every size bounded by the algebra universe. -/
@[stacks 0CS6 "limits of underlying rings of commutative algebras"]
instance forget₂CommRing_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (CommAlgCat.{w} R) CommRingCat.{w}) :=
  forgetToCommRing_preservesLimitsOfSize_of_univLE

end CommAlgCat
