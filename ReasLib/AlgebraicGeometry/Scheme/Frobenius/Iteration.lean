/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic

/-!
# Iterates of absolute Frobenius

This leaf owns the iterated absolute Frobenius and its basic computation and
naturality interfaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The `n`-fold absolute Frobenius of a scheme in characteristic `p`. -/
def absoluteFrobeniusPow (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] : ℕ → (S ⟶ S)
  | 0 => 𝟙 S
  | n + 1 => absoluteFrobeniusPow p S n ≫ absoluteFrobenius p S

/-- The zeroth absolute-Frobenius iterate is the identity morphism. -/
theorem absoluteFrobeniusPow_zero (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] :
    absoluteFrobeniusPow p S 0 = 𝟙 S := sorry

/-- The successor of an absolute-Frobenius iterate is obtained by postcomposing
with one absolute Frobenius. -/
theorem absoluteFrobeniusPow_succ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] (n : ℕ) :
    absoluteFrobeniusPow p S (n + 1) =
      absoluteFrobeniusPow p S n ≫ absoluteFrobenius p S := sorry

/-- The first absolute-Frobenius iterate is the ordinary absolute Frobenius. -/
theorem absoluteFrobeniusPow_one (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] :
    absoluteFrobeniusPow p S 1 = absoluteFrobenius p S := sorry

/-- The absolute Frobenius is the first absolute-Frobenius iterate. -/
theorem absoluteFrobenius_eq_absoluteFrobeniusPow_one (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] :
    absoluteFrobenius p S = absoluteFrobeniusPow p S 1 := sorry

/-- Iterating absolute Frobenius for `m + n` steps agrees with composing the
`m`-fold and `n`-fold iterates. -/
theorem absoluteFrobeniusPow_add (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] (m n : ℕ) :
    absoluteFrobeniusPow p S (m + n) =
      absoluteFrobeniusPow p S m ≫ absoluteFrobeniusPow p S n := sorry

/-- One absolute Frobenius commutes with each of its iterates. -/
theorem absoluteFrobeniusPow_left_comm (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [Scheme.IsCharP S p] (n : ℕ) :
    absoluteFrobenius p S ≫ absoluteFrobeniusPow p S n =
      absoluteFrobeniusPow p S n ≫ absoluteFrobenius p S := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- The iterated absolute Frobenius of the source of a morphism to a
characteristic-`p` scheme. -/
def absoluteFrobeniusPowSource (n : ℕ) : X ⟶ X :=
  @Scheme.absoluteFrobeniusPow p _ X (isCharP_of_target (p := p) f) n

/-- Iterated absolute Frobenius is natural for a scheme morphism to a
characteristic-`p` target. -/
theorem absoluteFrobeniusPow_comm (n : ℕ) :
    absoluteFrobeniusPowSource (p := p) f n ≫ f =
      f ≫ Scheme.absoluteFrobeniusPow p S n := sorry

end AlgebraicGeometry.Scheme.Hom
