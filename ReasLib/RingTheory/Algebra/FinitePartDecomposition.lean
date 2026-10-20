/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.CommAlgCat.Finite
public import ReasLib.RingTheory.QuasiFinite.Fiber.Dimension

@[expose] public section

/-!
# Algebra decompositions with a finite part

This leaf owns the concrete data of an algebra equivalence from an algebra to
the product of a module-finite algebra and a residual algebra.  Conditions on
the residual factor are parameterized by a selected base prime, so they can be
used independently of henselian-local-ring criteria.
-/

universe u v

namespace Algebra

/-- A decomposition of an `R`-algebra into a module-finite part and a residual
`R`-algebra. The finite part may use the ambient universe needed for both the
base and source, while the residual part remains in the source universe. -/
@[stacks 04GG "finite-part algebra decomposition"]
structure FinitePartDecomposition (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] where
  /-- The module-finite factor. -/
  finitePart : CommAlgCat.Finite.{max u v} R
  /-- The residual factor. -/
  remainder : CommAlgCat.{v} R
  /-- The algebra equivalence presenting the source as the two-factor product. -/
  equiv : S ≃ₐ[R] finitePart × remainder

namespace FinitePartDecomposition

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Build a finite-part decomposition from concrete factors and an algebra
equivalence to their product. -/
@[stacks 04GG "finite-part algebra decomposition constructor"]
def of (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (B : Type v) [CommRing B] [Algebra R B]
    (equiv : S ≃ₐ[R] A × B) : FinitePartDecomposition R S where
  finitePart := CommAlgCat.Finite.of R A
  remainder := CommAlgCat.of R B
  equiv := equiv

/-- The finite part supplied to `FinitePartDecomposition.of` is recovered by
projection. -/
@[stacks 04GG "finite-part decomposition finite factor", simp]
theorem finitePart_of (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (B : Type v) [CommRing B] [Algebra R B]
    (equiv : S ≃ₐ[R] A × B) :
    (of (R := R) (S := S) A B equiv).finitePart = CommAlgCat.Finite.of R A := sorry

/-- The residual factor supplied to `FinitePartDecomposition.of` is recovered
by projection. -/
@[stacks 04GG "finite-part decomposition residual factor", simp]
theorem remainder_of (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (B : Type v) [CommRing B] [Algebra R B]
    (equiv : S ≃ₐ[R] A × B) :
    (of (R := R) (S := S) A B equiv).remainder = CommAlgCat.of R B := sorry

/-- The algebra equivalence supplied to `FinitePartDecomposition.of` is
recovered by projection. -/
@[stacks 04GG "finite-part decomposition equivalence", simp]
theorem equiv_of (A : Type (max u v)) [CommRing A] [Algebra R A] [Module.Finite R A]
    (B : Type v) [CommRing B] [Algebra R B]
    (equiv : S ≃ₐ[R] A × B) :
    (of (R := R) (S := S) A B equiv).equiv = equiv := sorry

/-- A finite-part decomposition has a module-finite first factor and a
bijective algebra equivalence to the product of its factors. -/
theorem spec (D : FinitePartDecomposition R S) :
    Module.Finite R D.finitePart ∧ Function.Bijective D.equiv := sorry

/-- The residual factor has no quasi-finite points over a selected base prime. -/
@[stacks 04GG "finite-part remainder without quasi-finite points"]
def noQuasiFinitePoints
    (D : FinitePartDecomposition R S) (p : PrimeSpectrum R) : Prop :=
  ∀ q : p.asIdeal.primesOver D.remainder,
    ¬ Algebra.QuasiFiniteAt R q.1

/-- Every minimal-prime component of the residual factor's fiber over a
selected base prime has positive Krull dimension. -/
@[stacks 04GG "finite-part remainder positive-dimensional fiber"]
def positiveDimensionalFiber
    (D : FinitePartDecomposition R S) (p : PrimeSpectrum R) : Prop :=
  Algebra.Fiber.minimalPrimesPositiveDimensional (S := D.remainder) p

/-- The residual factor has a subsingleton residue-field fiber over a selected
base prime. -/
@[stacks 04GG "finite-part remainder subsingleton fiber"]
def subsingletonFiber
    (D : FinitePartDecomposition R S) (p : PrimeSpectrum R) : Prop :=
  Subsingleton (p.asIdeal.Fiber D.remainder)

/-- For a finite-type residual algebra, having no quasi-finite point over a
base prime is equivalent to positive-dimensional minimal-prime fiber
components. -/
@[stacks 04GG "finite-part remainder fiber dimension criterion"]
theorem noQuasiFinitePoints_iff_positiveDimensionalFiber
    (D : FinitePartDecomposition R S) [Algebra.FiniteType R D.remainder]
    (p : PrimeSpectrum R) :
    D.noQuasiFinitePoints p ↔ D.positiveDimensionalFiber p := sorry

end FinitePartDecomposition

end Algebra
