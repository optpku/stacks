/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Order.Directed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Divisibility Order on a Submonoid

Elements of a multiplicative submonoid
are ordered by divisibility in the ambient monoid.  The wrapper is necessary
because the inherited order on a submonoid has different meaning.
-/

@[expose] public section

universe u

namespace Submonoid

section Preorder

variable {R : Type u} [Monoid R]

/-- Elements of a submonoid viewed with the preorder induced by
divisibility in the ambient monoid. -/
@[stacks 00CR "submonoid divisibility index"]
def Divisibility (S : Submonoid R) : Type u := ULift.{0} S

/-- A submonoid element regarded as a divisibility index. -/
def Divisibility.mk {S : Submonoid R} (element : S) : S.Divisibility :=
  ULift.up element

/-- The underlying submonoid element of a divisibility index. -/
def Divisibility.val {S : Submonoid R} (index : S.Divisibility) : S :=
  ULift.down index

/-- The underlying submonoid element of a divisibility index. -/
@[stacks 00CR "submonoid divisibility coercion"]
instance divisibilityCoeSubmonoid (S : Submonoid R) : CoeTC S.Divisibility S :=
  ⟨Divisibility.val⟩

/-- The ambient monoid element underlying a divisibility index. -/
@[stacks 00CR "ambient divisibility coercion"]
instance divisibilityCoe (S : Submonoid R) : CoeTC S.Divisibility R :=
  ⟨fun s ↦ (s.val : R)⟩

/-- A submonoid element regarded as its divisibility index. -/
@[stacks 00CR "submonoid divisibility constructor coercion"]
instance divisibilityCoeOfSubmonoid (S : Submonoid R) : CoeTC S S.Divisibility :=
  ⟨Divisibility.mk⟩

/-- Coercing a submonoid element into the divisibility index and back is the
identity. -/
@[simp, stacks 00CR "submonoid divisibility coercion round trip"]
theorem divisibility_val_mk {S : Submonoid R} (s : S) :
    ((Divisibility.mk s : S.Divisibility) : S) = s := sorry

/-- The ambient value of a divisibility index made from a submonoid element is
the original ambient value. -/
@[simp, stacks 00CR "ambient divisibility coercion round trip"]
theorem divisibility_coe_mk {S : Submonoid R} (s : S) :
    ((Divisibility.mk s : S.Divisibility) : R) = s := sorry

/-- The order relation on divisibility indices. -/
@[stacks 00CR "submonoid divisibility order"]
instance divisibilityLE (S : Submonoid R) : LE S.Divisibility where
  le a b := (a : R) ∣ (b : R)

/-- The divisibility relation on a submonoid is a preorder. -/
@[stacks 00CR "submonoid divisibility preorder"]
instance divisibilityPreorder (S : Submonoid R) : Preorder S.Divisibility where
  le := (· ≤ ·)
  le_refl index := dvd_refl (index : R)
  le_trans _ _ _ := dvd_trans

/-- The unit element supplies a canonical divisibility index. -/
@[stacks 00CR "submonoid divisibility nonempty"]
instance divisibilityNonempty (S : Submonoid R) : Nonempty S.Divisibility :=
  ⟨Divisibility.mk 1⟩

end Preorder

section Directed

variable {R : Type u} [CommMonoid R]

/-- The divisibility preorder on a commutative submonoid is
directed, with products as common upper bounds. -/
@[stacks 00CR "directed submonoid divisibility index"]
instance divisibilityIsDirectedOrder (S : Submonoid R) : IsDirectedOrder S.Divisibility where
  directed _ _ := sorry

end Directed

end Submonoid
