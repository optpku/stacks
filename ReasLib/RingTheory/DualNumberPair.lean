/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/-- The commutative ring `DualNumberPair R` of a pair of square-zero directions over `R`. -/
abbrev DualNumberPair (R : Type u) : Type u :=
  TrivSqZeroExt R (R × R)

/-- The first square-zero generator of `DualNumberPair R`. -/
def DualNumberPair.eps1 {R : Type u} [CommRing R] : DualNumberPair R :=
  TrivSqZeroExt.inr (1, 0)

/-- The second square-zero generator of `DualNumberPair R`. -/
def DualNumberPair.eps2 {R : Type u} [CommRing R] : DualNumberPair R :=
  TrivSqZeroExt.inr (0, 1)

/-- The notation `ε₁` for the first square-zero generator. -/
scoped[DualNumberPair] notation "ε₁" => DualNumberPair.eps1

/-- The notation `ε₂` for the second square-zero generator. -/
scoped[DualNumberPair] notation "ε₂" => DualNumberPair.eps2

namespace DualNumberPair

variable (R : Type u) [CommRing R]

/-- The first square-zero generator has square zero. -/
theorem eps1_mul_eps1 : eps1 * eps1 = (0 : DualNumberPair R) := sorry

/-- The second square-zero generator has square zero. -/
theorem eps2_mul_eps2 : eps2 * eps2 = (0 : DualNumberPair R) := sorry

/-- The two square-zero generators have zero product. -/
theorem eps1_mul_eps2 : eps1 * eps2 = (0 : DualNumberPair R) := sorry

/-- The algebra projection retaining the first square-zero direction. -/
def projFst : DualNumberPair R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.fst R R R)

/-- The algebra projection retaining the second square-zero direction. -/
def projSnd : DualNumberPair R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.snd R R R)

/-- The first projection maps `ε₁` to the dual-number generator. -/
theorem projFst_eps1 : projFst R eps1 = DualNumber.eps := sorry

/-- The first projection maps `ε₂` to zero. -/
theorem projFst_eps2 : projFst R eps2 = 0 := sorry

/-- The second projection maps `ε₁` to zero. -/
theorem projSnd_eps1 : projSnd R eps1 = 0 := sorry

/-- The second projection maps `ε₂` to the dual-number generator. -/
theorem projSnd_eps2 : projSnd R eps2 = DualNumber.eps := sorry

/-- The square of coordinate rings defined by the two projections is a pullback. -/
theorem isPullback :
    IsPullback
      (CommRingCat.ofHom (projFst R).toRingHom)
      (CommRingCat.ofHom (projSnd R).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) :=
  sorry

/-- The `R`-algebra homomorphism `DualNumberPair R →ₐ[R] DualNumber R` sending
`ε₁` and `ε₂` to `ε`. -/
def sumAlgHom : DualNumberPair R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)

/-- The sum algebra homomorphism sends the first square-zero generator to `ε`. -/
theorem sumAlgHom_eps1 : sumAlgHom R eps1 = DualNumber.eps := sorry

/-- The sum algebra homomorphism sends the second square-zero generator to `ε`. -/
theorem sumAlgHom_eps2 : sumAlgHom R eps2 = DualNumber.eps := sorry

noncomputable section

/-- The scheme morphism induced by `sumAlgHom`, from the dual-number spectrum
to the spectrum of the pair of square-zero directions. -/
def sum :
    Spec (CommRingCat.of (DualNumber R)) ⟶ Spec (CommRingCat.of (DualNumberPair R)) :=
  Spec.map (CommRingCat.ofHom (sumAlgHom R).toRingHom)

end

end DualNumberPair
