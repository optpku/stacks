/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Computations

/-!
# Bilimit property of walking-cospan pseudocones

This leaf is the universal-property boundary for readable pseudopullback cones. The predicate is
only a presentation-level view of the neutral Yoneda condition on `PseudoCone`; construction and
field computations remain available from the preceding leaves.

This separation follows Stacks 003O/003Q: the square data and its component formulas are not
the finality assertion that characterizes a 2-fibre product.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The bilimit predicate for a readable pseudopullback square.

This is only a presentation-level abbreviation: the universal property remains the neutral
Yoneda condition owned by `PseudoCone.IsBilimit`. -/
abbrev IsBilimit (S : PseudoPullbackCone f g) : Prop :=
  S.toPseudoCone.IsBilimit

/-- Passing from a generic walking-cospan pseudocone to its readable normalization preserves and
reflects the bilimit universal property. -/
theorem ofPseudoCone.isBilimit_iff (s : PseudoCone (cospan f g)) :
    (ofPseudoCone s).IsBilimit ↔ s.IsBilimit := sorry
/- Proof strategy: compare the represented comparison functors for
`(ofPseudoCone s).toPseudoCone` and `s` through the two generating naturality isomorphisms.
Equivalence of categories is invariant under those natural isomorphisms. -/

/-- A generic bilimit walking-cospan pseudocone remains bilimit after passage to the readable
pseudopullback presentation. -/
instance ofPseudoCone.isBilimit (s : PseudoCone (cospan f g)) [s.IsBilimit] :
    (ofPseudoCone s).IsBilimit := sorry
/- Proof strategy: use the forward implication of `ofPseudoCone.isBilimit_iff`. -/

/- Data audit (mathlib 4.32): `IsBilimit` is a Prop-valued abbreviation and the bridge theorem
and instance defer only universal-property proofs; no concrete cone data are selected here. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
