module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Veronese rings

The `d`-Veronese ring of a nonnegatively graded commutative ring is the direct sum of the
homogeneous pieces whose degrees are multiples of `d`.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

universe u

namespace GradedRing.Veronese

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-`n` homogeneous piece of the `d`-Veronese ring. -/
abbrev degree (d n : ℕ) : Type u :=
  𝒜 (n * d)

end GradedRing.Veronese

namespace GradedRing

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- The `d`-Veronese ring of a nonnegatively graded commutative ring. -/
abbrev Veronese (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : Type u :=
  ⨁ n : ℕ, Veronese.degree 𝒜 d n

namespace Veronese

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The unit in degree zero of the `d`-Veronese grading. -/
abbrev one (d : ℕ) : degree 𝒜 d 0 :=
  Eq.mp (congrArg (fun i : ℕ ↦ (𝒜 i : Type u)) (Nat.zero_mul d).symm) (1 : 𝒜 0)

/-- Multiplication of two homogeneous pieces of the `d`-Veronese grading. -/
abbrev mul (d m n : ℕ) :
    degree 𝒜 d m → degree 𝒜 d n → degree 𝒜 d (m + n) :=
  fun x y ↦
    Eq.mp (congrArg (fun i : ℕ ↦ (𝒜 i : Type u)) (Nat.add_mul m n d).symm) <|
      (⟨(x : A) * (y : A), SetLike.mul_mem_graded x.prop y.prop⟩ : 𝒜 (m * d + n * d))

/-- The Veronese unit supplies the canonical graded unit. -/
noncomputable instance instGOne (d : ℕ) :
    GradedMonoid.GOne (degree 𝒜 d) where
  one := one 𝒜 d

/-- Multiplication by zero on the right vanishes in homogeneous Veronese pieces. -/
theorem mul_zero (d : ℕ) {m n : ℕ} (x : degree 𝒜 d m) :
    mul 𝒜 d m n x (0 : degree 𝒜 d n) = 0 := sorry

/-- Multiplication by zero on the left vanishes in homogeneous Veronese pieces. -/
theorem zero_mul (d : ℕ) {m n : ℕ} (y : degree 𝒜 d n) :
    mul 𝒜 d m n (0 : degree 𝒜 d m) y = 0 := sorry

/-- Homogeneous Veronese multiplication distributes over addition on the right. -/
theorem mul_add (d : ℕ) {m n : ℕ}
    (x : degree 𝒜 d m) (y z : degree 𝒜 d n) :
    mul 𝒜 d m n x (y + z) = mul 𝒜 d m n x y + mul 𝒜 d m n x z := sorry

/-- Homogeneous Veronese multiplication distributes over addition on the left. -/
theorem add_mul (d : ℕ) {m n : ℕ}
    (x y : degree 𝒜 d m) (z : degree 𝒜 d n) :
    mul 𝒜 d m n (x + y) z = mul 𝒜 d m n x z + mul 𝒜 d m n y z := sorry

/-- The homogeneous Veronese multiplication is additive in both variables. -/
noncomputable instance instGNonUnitalNonAssocSemiring (d : ℕ) :
    DirectSum.GNonUnitalNonAssocSemiring (degree 𝒜 d) where
  mul := fun {m n} x y ↦ mul 𝒜 d m n x y
  mul_zero := mul_zero 𝒜 d
  zero_mul := zero_mul 𝒜 d
  mul_add := mul_add 𝒜 d
  add_mul := add_mul 𝒜 d

/-- The graded Veronese unit is a left identity. -/
theorem one_mul (d : ℕ) (x : GradedMonoid (degree 𝒜 d)) :
    (1 : GradedMonoid (degree 𝒜 d)) * x = x := sorry

/-- The graded Veronese unit is a right identity. -/
theorem mul_one (d : ℕ) (x : GradedMonoid (degree 𝒜 d)) :
    x * (1 : GradedMonoid (degree 𝒜 d)) = x := sorry

/-- Homogeneous Veronese multiplication is associative. -/
theorem mul_assoc (d : ℕ) (x y z : GradedMonoid (degree 𝒜 d)) :
    x * y * z = x * (y * z) := sorry

/-- The default zeroth graded power is the Veronese unit. -/
theorem gnpow_zero (d : ℕ) (x : GradedMonoid (degree 𝒜 d)) :
    GradedMonoid.mk _ (GradedMonoid.GMonoid.gnpowRec 0 x.snd) = 1 := sorry

/-- The default successor graded power is multiplication by its base. -/
theorem gnpow_succ (d : ℕ) (n : ℕ) (x : GradedMonoid (degree 𝒜 d)) :
    GradedMonoid.mk _ (GradedMonoid.GMonoid.gnpowRec n.succ x.snd) =
      GradedMonoid.mk _ (GradedMonoid.GMonoid.gnpowRec n x.snd) * x := sorry

/-- The homogeneous Veronese pieces form a graded monoid. -/
noncomputable instance instGMonoid (d : ℕ) :
    GradedMonoid.GMonoid (degree 𝒜 d) where
  one_mul := one_mul 𝒜 d
  mul_one := mul_one 𝒜 d
  mul_assoc := mul_assoc 𝒜 d
  gnpow_zero' := gnpow_zero 𝒜 d
  gnpow_succ' := gnpow_succ 𝒜 d

/-- Homogeneous Veronese multiplication is commutative. -/
theorem mul_comm (d : ℕ) (x y : GradedMonoid (degree 𝒜 d)) :
    x * y = y * x := sorry

/-- The homogeneous Veronese pieces form a graded commutative monoid. -/
noncomputable instance instGCommMonoid (d : ℕ) :
    GradedMonoid.GCommMonoid (degree 𝒜 d) where
  mul_comm := mul_comm 𝒜 d

/-- The canonical natural-number cast in degree zero sends zero to zero. -/
theorem natCast_zero (d : ℕ) :
    (0 : ℕ) • one 𝒜 d = 0 := sorry

/-- The canonical natural-number cast in degree zero respects successors. -/
theorem natCast_succ (d n : ℕ) :
    (n + 1) • one 𝒜 d = n • one 𝒜 d + one 𝒜 d := sorry

/-- The homogeneous Veronese pieces form a graded semiring. -/
noncomputable instance instGSemiring (d : ℕ) :
    DirectSum.GSemiring (degree 𝒜 d) :=
  { (inferInstance : DirectSum.GNonUnitalNonAssocSemiring (degree 𝒜 d)),
    (inferInstance : GradedMonoid.GMonoid (degree 𝒜 d)) with
    natCast := fun n ↦ n • one 𝒜 d
    natCast_zero := natCast_zero 𝒜 d
    natCast_succ := natCast_succ 𝒜 d }

/-- The canonical integer cast extends the natural-number cast. -/
theorem intCast_ofNat (d n : ℕ) :
    (n : ℤ) • one 𝒜 d = n • one 𝒜 d := sorry

/-- The canonical integer cast has the expected negative-successor value. -/
theorem intCast_negSucc (d n : ℕ) :
    Int.negSucc n • one 𝒜 d = -((n + 1) • one 𝒜 d) := sorry

/-- The homogeneous Veronese pieces form a graded ring. -/
noncomputable instance instGRing (d : ℕ) :
    DirectSum.GRing (degree 𝒜 d) :=
  { (inferInstance : DirectSum.GSemiring (degree 𝒜 d)) with
    intCast := fun z ↦ z • one 𝒜 d
    intCast_ofNat := intCast_ofNat 𝒜 d
    intCast_negSucc_ofNat := intCast_negSucc 𝒜 d }

/-- The homogeneous Veronese pieces form a graded commutative semiring. -/
noncomputable instance instGCommSemiring (d : ℕ) :
    DirectSum.GCommSemiring (degree 𝒜 d) :=
  { (inferInstance : DirectSum.GSemiring (degree 𝒜 d)),
    (inferInstance : GradedMonoid.GCommMonoid (degree 𝒜 d)) with }

/-- The `d`-Veronese direct sum has its canonical commutative-ring structure. -/
noncomputable instance instGCommRing (d : ℕ) :
    DirectSum.GCommRing (degree 𝒜 d) :=
  { (inferInstance : DirectSum.GRing (degree 𝒜 d)),
    (inferInstance : DirectSum.GCommSemiring (degree 𝒜 d)) with }

end Veronese

end GradedRing
