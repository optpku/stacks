/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.Operational
public import Mathlib.Algebra.DirectSum.Ring

/-! # The graded ring of operational Chow classes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OperationalChow

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

/-- A cap family is compatible when it commutes with proper pushforward,
flat pullback, and refined Cartier Gysin maps. -/
def Compatible {p : ℤ} (c : CapFamily δ f p) : Prop :=
  CompatibleWithProperPushforward δ f c ∧
    CompatibleWithFlatPullback δ f c ∧ CompatibleWithCartierGysin δ f c

/-- Composition of cap families, with the right factor acting first. -/
def mulFamily {p q : ℤ} (c : CapFamily δ f p) (d : CapFamily δ f q) :
    CapFamily δ f (p + q) :=
  fun {Y} g _ _ k ↦
    ((AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
      (show k - q - p = k - (p + q) by omega)).toAddMonoidHom).comp
        ((c g (k - q)).comp (d g k))

/-- The degree-zero cap family acting by the identity on each Chow group. -/
def oneFamily : CapFamily δ f 0 :=
  fun {_} g _ _ k ↦
    (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom

namespace Graded

/-- The zero cap family satisfies all three compatibility laws. -/
theorem compatible_zero (p : ℤ) : Compatible δ f ((instAddCommGroupCapFamily δ f p).zero) := sorry

/-- The sum of two compatible cap families is compatible. -/
theorem compatible_add {p : ℤ} (c d : CapFamily δ f p)
    (hc : Compatible δ f c) (hd : Compatible δ f d) :
    Compatible δ f ((instAddCommGroupCapFamily δ f p).add c d) := sorry

/-- The negative of a compatible cap family is compatible. -/
theorem compatible_neg {p : ℤ} (c : CapFamily δ f p) (hc : Compatible δ f c) :
    Compatible δ f ((instAddCommGroupCapFamily δ f p).neg c) := sorry

/-- Composition preserves the three compatibility laws. -/
theorem compatible_mul {p q : ℤ} (c : CapFamily δ f p) (d : CapFamily δ f q)
    (hc : Compatible δ f c) (hd : Compatible δ f d) :
    Compatible δ f (mulFamily δ f c d) := sorry

/-- The identity cap family satisfies the three compatibility laws. -/
theorem compatible_one : Compatible δ f (oneFamily δ f) := sorry

end Graded

/-- The additive subgroup of cap families satisfying all three compatibility laws. -/
def compatibleFamilies (p : ℤ) : AddSubgroup (CapFamily δ f p) where
  carrier := fun c ↦ Compatible δ f c
  zero_mem' := Graded.compatible_zero δ f p
  add_mem' := Graded.compatible_add δ f _ _
  neg_mem' := Graded.compatible_neg δ f _

/-- The degree-`p` additive group of compatible operational cap families. -/
abbrev Graded (p : ℤ) : Type _ := compatibleFamilies δ f p

namespace Graded

/-- The underlying cap action of a compatible graded family. -/
def cap {p : ℤ} (c : Graded δ f p) : CapFamily δ f p := c.val

/-- Regard an explicit operational class as an element of the compatible subgroup. -/
def ofOperational {p : ℤ} (c : OperationalChow δ f p) : Graded δ f p :=
  ⟨c.cap, c.map_proper, c.pullback_flat, c.gysin_cartier⟩

/-- Regard a compatible graded family as an explicit operational class. -/
def toOperational {p : ℤ} (c : Graded δ f p) : OperationalChow δ f p :=
  ofCap δ f c.val c.property.1 c.property.2.1 c.property.2.2

/-- Converting an operational class to the subgroup preserves its cap action. -/
theorem ofOperational_cap {p : ℤ} (c : OperationalChow δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    cap δ f (ofOperational δ f c) g k = c.cap g k := rfl

/-- Converting a subgroup element to an operational class preserves its cap action. -/
theorem toOperational_cap {p : ℤ} (c : Graded δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (toOperational δ f c).cap g k = cap δ f c g k := rfl

/-- The graded product is composition of the underlying cap actions. -/
def mul {p q : ℤ} (c : Graded δ f p) (d : Graded δ f q) : Graded δ f (p + q) :=
  ⟨mulFamily δ f c.val d.val, compatible_mul δ f c.val d.val c.property d.property⟩

/-- The graded unit acts by the identity on Chow groups. -/
def one : Graded δ f 0 := ⟨oneFamily δ f, compatible_one δ f⟩

/-- A natural number acts as the corresponding multiple of the graded unit. -/
def natCast (n : ℕ) : Graded δ f 0 := n • one δ f

/-- An integer acts as the corresponding multiple of the graded unit. -/
def intCast (n : ℤ) : Graded δ f 0 := n • one δ f

/-- Composition with the zero cap action on the right vanishes. -/
theorem mul_zero {p q : ℤ} (c : Graded δ f p) :
    mul δ f c (0 : Graded δ f q) = 0 := sorry

/-- Composition with the zero cap action on the left vanishes. -/
theorem zero_mul {p q : ℤ} (d : Graded δ f q) :
    mul δ f (0 : Graded δ f p) d = 0 := sorry

/-- Graded composition distributes over addition in its right argument. -/
theorem mul_add {p q : ℤ} (c : Graded δ f p) (d e : Graded δ f q) :
    mul δ f c (d + e) = mul δ f c d + mul δ f c e := sorry

/-- Graded composition distributes over addition in its left argument. -/
theorem add_mul {p q : ℤ} (c d : Graded δ f p) (e : Graded δ f q) :
    mul δ f (c + d) e = mul δ f c e + mul δ f d e := sorry

/-- The identity cap action is a left unit in the graded family. -/
theorem one_mul (c : GradedMonoid (Graded δ f)) :
    GradedMonoid.mk (0 + c.1) (mul δ f (one δ f) c.2) = c := sorry

/-- The identity cap action is a right unit in the graded family. -/
theorem mul_one (c : GradedMonoid (Graded δ f)) :
    GradedMonoid.mk (c.1 + 0) (mul δ f c.2 (one δ f)) = c := sorry

/-- Composition of compatible cap actions is associative. -/
theorem mul_assoc (c d e : GradedMonoid (Graded δ f)) :
    GradedMonoid.mk ((c.1 + d.1) + e.1) (mul δ f (mul δ f c.2 d.2) e.2) =
      GradedMonoid.mk (c.1 + (d.1 + e.1)) (mul δ f c.2 (mul δ f d.2 e.2)) := sorry

/-- The natural-number cast sends zero to zero. -/
theorem natCast_zero : natCast δ f 0 = 0 := sorry

/-- The natural-number cast sends successors to addition of the unit. -/
theorem natCast_succ (n : ℕ) : natCast δ f (n + 1) = natCast δ f n + one δ f := sorry

/-- The integer cast extends the natural-number cast. -/
theorem intCast_ofNat (n : ℕ) : intCast δ f n = natCast δ f n := sorry

/-- The integer cast sends negative successors to negative natural multiples. -/
theorem intCast_negSucc (n : ℕ) : intCast δ f (Int.negSucc n) = -natCast δ f (n + 1) := sorry

/-- Compatible cap families form a graded ring under shifted composition,
with natural powers given by the canonical graded multiplication recursion. -/
instance instGRing : DirectSum.GRing (Graded δ f) where
  mul := mul δ f
  one := one δ f
  mul_zero := mul_zero δ f
  zero_mul := zero_mul δ f
  mul_add := mul_add δ f
  add_mul := add_mul δ f
  one_mul := one_mul δ f
  mul_one := mul_one δ f
  mul_assoc := mul_assoc δ f
  gnpow := @GradedMonoid.GMonoid.gnpowRec ℤ (Graded δ f) _
    ⟨mul δ f⟩ ⟨one δ f⟩
  gnpow_zero' := @GradedMonoid.GMonoid.gnpowRec_zero ℤ (Graded δ f) _
    ⟨mul δ f⟩ ⟨one δ f⟩
  gnpow_succ' := @GradedMonoid.GMonoid.gnpowRec_succ ℤ (Graded δ f) _
    ⟨mul δ f⟩ ⟨one δ f⟩
  natCast := natCast δ f
  natCast_zero := natCast_zero δ f
  natCast_succ := natCast_succ δ f
  intCast := intCast δ f
  intCast_ofNat := intCast_ofNat δ f
  intCast_negSucc_ofNat := intCast_negSucc δ f

end Graded

/-- The integer-graded direct sum of compatible operational cap families. -/
abbrev ring := ⨁ p : ℤ, Graded δ f p

/-- The direct sum of compatible operational cap families is a ring. -/
instance instRing : Ring (ring δ f) := DirectSum.ring (Graded δ f)

/-- Compose two explicit operational classes, with the right factor acting first. -/
def mul {p q : ℤ} (c : OperationalChow δ f p) (d : OperationalChow δ f q) :
    OperationalChow δ f (p + q) :=
  Graded.toOperational δ f (Graded.mul δ f
    (Graded.ofOperational δ f c) (Graded.ofOperational δ f d))

/-- Include a homogeneous operational class in the operational Chow ring. -/
def homogeneous (p : ℤ) (c : OperationalChow δ f p) : ring δ f :=
  DirectSum.of (Graded δ f) p (Graded.ofOperational δ f c)

/-- Multiplication of homogeneous inclusions agrees with cap composition. -/
theorem homogeneous_mul {p q : ℤ} (c : OperationalChow δ f p) (d : OperationalChow δ f q) :
    homogeneous δ f p c * homogeneous δ f q d =
      homogeneous δ f (p + q) (mul δ f c d) := sorry

end AlgebraicGeometry.AlgebraicSpace.OperationalChow
