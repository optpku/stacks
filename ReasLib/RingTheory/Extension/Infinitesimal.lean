/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Infinitesimal Extensions

The infinitesimal extension of any algebra extension has the canonical
square-zero kernel.  This is a property of the standard cotangent ideal, not
of a chosen presentation or a first-order universality witness.

@stack 04EC
-/

@[expose] public section

namespace Algebra.Extension

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

@[simp, stacks 04EC "square-zero infinitesimal kernel"]
theorem infinitesimal_ker_sq_eq_bot (P : Extension.{w} R S) :
    P.infinitesimal.ker ^ 2 = ⊥ := by
  rw [ker_infinitesimal]
  exact Ideal.cotangentIdeal_square P.ker

namespace Infinitesimal

set_option backward.isDefEq.respectTransparency false in
/-- The canonical quotient-algebra structure of `P.Ring / P.ker²` on the
source ring of `P.infinitesimal`.

This is a named, reducible choice rather than a global instance: if the base
ring type is definitionally `P.Ring`, it can compete with the algebra structure
inherited from `P.infinitesimal` as an extension. -/
@[instance_reducible, stacks 04EC "infinitesimal quotient algebra"]
noncomputable def algebra (P : Extension.{w} R S) :
    Algebra P.Ring P.infinitesimal.Ring :=
  inferInstanceAs (Algebra P.Ring (P.Ring ⧸ P.ker ^ 2))

-- Local instance justification (instance diamond): this computation rule
-- describes the named quotient action without registering it globally.
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebra in
@[simp, stacks 04EC "infinitesimal quotient algebra map"]
theorem algebraMap_apply (P : Extension.{w} R S) (x : P.Ring) :
    algebraMap P.Ring P.infinitesimal.Ring x =
      Ideal.Quotient.mk (P.ker ^ 2) x := rfl

-- Local instance justification (instance diamond): this declaration records
-- the tower for the named quotient action without making that action global.
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebra in
@[stacks 04EC "infinitesimal quotient scalar tower"]
instance sourceTower (P : Extension.{w} R S) :
    IsScalarTower R P.Ring P.infinitesimal.Ring :=
  inferInstanceAs (IsScalarTower R P.Ring (P.Ring ⧸ P.ker ^ 2))

-- Local instance justification (instance diamond): this declaration records
-- the target tower for the same named quotient action.
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebra in
@[stacks 04EC "infinitesimal quotient target tower"]
instance targetTower (P : Extension.{w} R S) :
    IsScalarTower P.Ring P.infinitesimal.Ring S :=
  .of_algebraMap_eq' rfl

-- Local instance justification (instance diamond): the named quotient action
-- is required to express this canonical inclusion linearly.
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebra in
/-- The cotangent ideal included in the ring of the infinitesimal extension. -/
@[stacks 04EC "cotangent ideal inclusion into an infinitesimal extension"]
noncomputable def cotangentIdealSubtype (P : Extension.{w} R S) :
    P.ker.cotangentIdeal →ₗ[P.Ring] P.infinitesimal.Ring :=
  P.ker.cotangentIdeal.subtype.restrictScalars P.Ring

-- Local instance justification (instance diamond): this computation rule must
-- use the same named quotient action as `cotangentIdealSubtype`.
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebra in
@[simp, stacks 04EC "cotangent ideal inclusion on elements"]
theorem cotangentIdealSubtype_apply (P : Extension.{w} R S)
    (x : P.ker.cotangentIdeal) :
    cotangentIdealSubtype P x = P.ker.cotangentIdeal.subtype x := rfl

end Infinitesimal

end Algebra.Extension
