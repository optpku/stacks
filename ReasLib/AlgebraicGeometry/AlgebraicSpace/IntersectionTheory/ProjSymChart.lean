/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.AffineProjSym
public import Mathlib.Algebra.MvPolynomial.Basic

/-! Explicit quotient-coordinate maps into the actual symmetric projective spectrum. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjSymChart
variable {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing A] [Algebra R A]

/-- A specified local trivialized quotient and a chosen generator of the line. -/
structure Datum where
  quotient : M →ₗ[R] A
  pivot : M
  pivot_one : quotient pivot = 1

variable (d : Datum (R := R) (M := M) (A := A))

/-- Universal symmetric-algebra evaluation; its generator formula is proved by Mathlib. -/
def evaluate : SymmetricAlgebra R M →ₐ[R] A := SymmetricAlgebra.lift d.quotient

@[simp] theorem evaluate_generator (m : M) : evaluate d (SymmetricAlgebra.ι R M m) = d.quotient m := by
  exact SymmetricAlgebra.lift_ι_apply d.quotient m

def awayVal : HomogeneousLocalization.Away (AffineProjSym.grading R M)
    (SymmetricAlgebra.ι R M d.pivot) →+* Localization.Away (SymmetricAlgebra.ι R M d.pivot) where
  toFun := HomogeneousLocalization.val
  map_one' := HomogeneousLocalization.val_one
  map_mul' := HomogeneousLocalization.val_mul
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

/-- The homogeneous localization map is evaluation with the pivot sent to1. -/
def coordinateMap : HomogeneousLocalization.Away (AffineProjSym.grading R M)
    (SymmetricAlgebra.ι R M d.pivot) →+* A :=
  (Localization.awayLift (evaluate d).toRingHom (SymmetricAlgebra.ι R M d.pivot) (by
    change IsUnit (evaluate d (SymmetricAlgebra.ι R M d.pivot))
    rw [evaluate_generator, d.pivot_one]
    exact isUnit_one)).comp (awayVal d)

/-- The real scheme morphism from quotient coordinates to Proj(Sym M). -/
def toProj : Spec (.of A) ⟶ AffineProjSym.scheme R M :=
  Spec.map (CommRingCat.ofHom (coordinateMap d)) ≫
    Proj.awayι (AffineProjSym.grading R M) (SymmetricAlgebra.ι R M d.pivot)
      (Proj.SymmetricQuotientChart.generator_mem_degreeOne d.pivot) (by decide)

/-- This map lies over the specified coefficient map. -/
theorem toProj_toSpec :
    toProj d ≫ AffineProjSym.toSpec R M = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  sorry

/-- Fraction coordinates recover precisely the quotient coefficients. -/
theorem coordinateMap_fraction (m : M) :
    coordinateMap d
      (HomogeneousLocalization.Away.mk (AffineProjSym.grading R M)
        (Proj.SymmetricQuotientChart.generator_mem_degreeOne d.pivot) 1
        (SymmetricAlgebra.ι R M m) (Proj.SymmetricQuotientChart.generator_mem_degreeOne m)) =
      d.quotient m := by
  sorry

section Free
variable (R) [Nontrivial R] (n : ℕ) (i : Fin n)

/-- The standard D+(X_i) coordinate ring uses exactly the non-pivot coordinates. -/
abbrev coordinateRing := MvPolynomial {j : Fin n // j ≠ i} R

def coefficient (j : Fin n) : coordinateRing R n i :=
  if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

/-- The free quotient sends e_i to1 and all other basis vectors to their variables. -/
def freeQuotient : (Fin n → R) →ₗ[R] coordinateRing R n i :=
  ∑ j : Fin n, (LinearMap.toSpanSingleton R (coordinateRing R n i) (coefficient R n i j)).comp
    (LinearMap.proj j)

theorem freeQuotient_single (j : Fin n) :
    freeQuotient R n i (Pi.single j (1 : R)) = coefficient R n i j := by
  classical
  simp [freeQuotient, LinearMap.toSpanSingleton_apply, Pi.single_apply]

def freeDatum : Datum (R := R) (M := Fin n → R) (A := coordinateRing R n i) where
  quotient := freeQuotient R n i
  pivot := Pi.single i 1
  pivot_one := by rw [freeQuotient_single]; simp [coefficient]

/-- Explicit free standard chart, including its map into the actual Proj. -/
def freeChart : Spec (.of (coordinateRing R n i)) ⟶ AffineProjSym.scheme R (Fin n → R) :=
  toProj (freeDatum R n i)

end Free
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjSymChart
