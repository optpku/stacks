/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Ideal.Principal

/-!
# Principal-power quotients of algebras

This file owns the quotient `A / π^n A` for an `R`-algebra `A`, its
functorial maps, and the canonical comparison from the square thickening to
the first-order thickening.  It replaces repeated local quotient and scalar
tower instances in principal-thickening arguments.
-/

@[expose] public section

noncomputable section

open scoped PrincipalIdeal

universe u v w x

namespace Algebra

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The quotient `A / π^n A`, formed by extending the principal-power ideal from the base. -/
@[stacks 07CP "principal-power quotient"]
abbrev PrincipalQuotient (π : R) (n : ℕ) :=
  A ⧸ Ideal.map (algebraMap R A) (principalPowerIdeal π n)

end Algebra

namespace Algebra.PrincipalQuotient

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The canonical algebra map from an algebra to its principal-power quotient. -/
@[stacks 07CP "principal-power quotient projection"]
def mk (π : R) (n : ℕ) :
    A →ₐ[R] Algebra.PrincipalQuotient R A π n :=
  Ideal.Quotient.mkₐ R _

/-- An algebra map induces a map on principal-power quotients of the same order. -/
@[stacks 07CR "principal-power quotient map"]
def map (f : A →ₐ[R] B) (π : R) (n : ℕ) :
    Algebra.PrincipalQuotient R A π n →ₐ[R ⧸ principalPowerIdeal π n]
      Algebra.PrincipalQuotient R B π n :=
  f.quotientByBaseIdeal (principalPowerIdeal π n)

/-- The principal-power quotient map sends a residue class to the class of its image. -/
@[simp]
theorem map_mk (f : A →ₐ[R] B) (π : R) (n : ℕ) (a : A) :
    map f π n (mk (A := A) π n a) = mk (A := B) π n (f a) := sorry

/-- Principal-power quotient maps preserve composition. -/
@[simp]
theorem map_comp {C : Type x} [CommRing C] [Algebra R C]
    (g : B →ₐ[R] C) (f : A →ₐ[R] B) (π : R) (n : ℕ) :
    (map g π n).comp (map f π n) = map (g.comp f) π n := sorry

/-- The principal-power quotient map induced by the identity is the identity. -/
@[simp]
theorem map_id (π : R) (n : ℕ) :
    map (AlgHom.id R A) π n =
      AlgHom.id (R ⧸ principalPowerIdeal π n)
        (Algebra.PrincipalQuotient R A π n) := sorry

namespace Square

/-- The square of a principal ideal lies in its first power. -/
theorem le_first (π : R) :
    principalPowerIdeal π 2 ≤ principalPowerIdeal π 1 := sorry

/-- The quotient `A / πA` is canonically an algebra over `R / π²R`. -/
@[stacks 07CP "first quotient over the square quotient"]
instance instAlgebraFirst (π : R) :
    Algebra (R ⧸ principalPowerIdeal π 2) (Algebra.PrincipalQuotient R A π 1) :=
  Ideal.Quotient.algebraQuotientOfLEComap <|
    (le_first π).trans Ideal.le_comap_map

/-- The canonical scalar structures on `A / πA` form a tower over `R / π²R`. -/
instance instIsScalarTowerFirst (π : R) :
    IsScalarTower R (R ⧸ principalPowerIdeal π 2)
      (Algebra.PrincipalQuotient R A π 1) := sorry

/-- The map on first principal quotients respects scalars from the square quotient of the base. -/
theorem mapFirst_commutes
    (f : A →ₐ[R] B) (π : R) (r : R ⧸ principalPowerIdeal π 2) :
    (map f π 1)
        (algebraMap (R ⧸ principalPowerIdeal π 2)
          (Algebra.PrincipalQuotient R A π 1) r) =
      algebraMap (R ⧸ principalPowerIdeal π 2)
        (Algebra.PrincipalQuotient R B π 1) r := sorry

/-- The first principal-quotient map, regarded over the square quotient of the base. -/
@[stacks 07CP "first principal-quotient map over the square quotient"]
def mapFirst (f : A →ₐ[R] B) (π : R) :
    Algebra.PrincipalQuotient R A π 1 →ₐ[R ⧸ principalPowerIdeal π 2]
      Algebra.PrincipalQuotient R B π 1 where
  toRingHom := (map f π 1).toRingHom
  commutes' := mapFirst_commutes f π

/-- The square-base map on first quotients sends a residue class to the class of its image. -/
@[simp]
theorem mapFirst_mk (f : A →ₐ[R] B) (π : R) (a : A) :
    mapFirst f π
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R A) (principalPowerIdeal π 1)) a) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R B) (principalPowerIdeal π 1)) (f a) := sorry

/-- The underlying quotient map from `A / π²A` to `A / πA`. -/
def reductionRingHom (π : R) :
    Algebra.PrincipalQuotient R A π 2 →+* Algebra.PrincipalQuotient R A π 1 :=
  Ideal.Quotient.factor <| Ideal.map_mono (le_first π)

/-- The square-to-first reduction commutes with scalars from `R / π²R`. -/
theorem reductionRingHom_commutes
    (π : R) (r : R ⧸ principalPowerIdeal π 2) :
    reductionRingHom (A := A) π
        (algebraMap (R ⧸ principalPowerIdeal π 2)
          (Algebra.PrincipalQuotient R A π 2) r) =
      algebraMap (R ⧸ principalPowerIdeal π 2)
        (Algebra.PrincipalQuotient R A π 1) r := sorry

/-- The canonical reduction map `A / π²A → A / πA`. -/
@[stacks 07CP "square-to-first principal quotient reduction"]
def reduction (π : R) :
    Algebra.PrincipalQuotient R A π 2 →ₐ[R ⧸ principalPowerIdeal π 2]
      Algebra.PrincipalQuotient R A π 1 where
  toRingHom := reductionRingHom π
  commutes' := reductionRingHom_commutes π

/-- Square-to-first reduction sends a residue class to the same representative class. -/
@[simp]
theorem reduction_mk (π : R) (a : A) :
    reduction (A := A) π
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R A) (principalPowerIdeal π 2)) a) =
      Ideal.Quotient.mk
        (Ideal.map (algebraMap R A) (principalPowerIdeal π 1)) a := sorry

/-- Square-to-first reduction is natural in the ambient algebra. -/
@[simp]
theorem reduction_naturality (f : A →ₐ[R] B) (π : R) :
    (reduction (A := B) π).comp (map f π 2) =
      (mapFirst f π).comp (reduction (A := A) π) := sorry

end Square

namespace FirstOrder

variable {C : Type w} [CommRing C]
variable (π : R) [Algebra (R ⧸ principalPowerIdeal π 2) C]

/-- The image in `C` of the first-order ideal inside `R / π²R`. -/
@[stacks 07CP "first-order ideal over a principal square quotient"]
abbrev ideal : Ideal C :=
  Ideal.map (algebraMap (R ⧸ principalPowerIdeal π 2) C)
    (principalIdeal (Ideal.Quotient.mk (principalPowerIdeal π 2) π))

/-- A map from `C` to an algebra killed by `π` kills the first-order ideal of `C`. -/
theorem ideal_le_ker
    (f : C →ₐ[R ⧸ principalPowerIdeal π 2] Algebra.PrincipalQuotient R A π 1) :
    ideal (C := C) π ≤ RingHom.ker f.toRingHom := sorry

/-- The canonical descended map from the first-order quotient of `C` to `A / πA`. -/
@[stacks 07CP "descent from the first-order quotient"]
def descend
    (f : C →ₐ[R ⧸ principalPowerIdeal π 2] Algebra.PrincipalQuotient R A π 1) :
    C ⧸ ideal (C := C) π →ₐ[R ⧸ principalPowerIdeal π 2]
      Algebra.PrincipalQuotient R A π 1 :=
  Ideal.Quotient.liftₐ _ f (ideal_le_ker π f)

/-- First-order descent sends the class of an element to its original image. -/
@[simp]
theorem descend_mk
    (f : C →ₐ[R ⧸ principalPowerIdeal π 2] Algebra.PrincipalQuotient R A π 1)
    (c : C) :
    descend π f (Ideal.Quotient.mk (ideal (C := C) π) c) = f c := sorry

/-- First-order descent composed with the quotient map is the original map. -/
@[simp]
theorem descend_comp_mk
    (f : C →ₐ[R ⧸ principalPowerIdeal π 2] Algebra.PrincipalQuotient R A π 1) :
    (descend π f).comp
        (Ideal.Quotient.mkₐ (R ⧸ principalPowerIdeal π 2) (ideal (C := C) π)) =
      f := sorry

end FirstOrder

end Algebra.PrincipalQuotient
