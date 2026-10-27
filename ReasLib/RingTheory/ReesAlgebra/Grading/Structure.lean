/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.Grading.Decomposition

/-!
# Structural Maps for a Graded Rees Algebra

This leaf supplies degree-one elements, functorial Rees-algebra maps, and the
degree-zero scalar algebra after the canonical grading has been constructed.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

namespace ReesAlgebra.Grading

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/-- The degree-one homogeneous element `a^(1) = a t` of `reesAlgebra I`. -/
@[stacks 052Q "degree-one Rees element"]
def degreeOne (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.1,
    (reesAlgebra.monomial_mem).2
      (Eq.mp (congrArg (fun J : Ideal R => a.1 ∈ J) (pow_one I).symm) a.2)⟩

/-- The polynomial underlying the degree-one Rees element `a^(1)` is
`monomial 1 a`. -/
@[stacks 052Q "degree-one Rees element evaluation", simp]
theorem degreeOne_apply (a : I) :
    ((degreeOne I a : reesAlgebra I) : R[X]) = monomial 1 a.1 := sorry

/-- The degree-one element `a^(1)` belongs to the first graded Rees piece. -/
@[stacks 052Q "degree-one Rees element membership"]
theorem degreeOne_mem (a : I) :
    degreeOne I a ∈ grade I 1 := sorry

/-- A ring map carrying `I` into `J` carries the Rees algebra of `I` into the
Rees algebra of `J`. -/
@[stacks 0BIP "Rees algebra map membership"]
theorem map_mem {I : Ideal R} {S : Type*} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (x : reesAlgebra I) :
    Polynomial.mapRingHom f x.1 ∈ reesAlgebra J := sorry

/-- The ring homomorphism of Rees algebras induced by a map carrying `I` into
`J`. -/
@[stacks 0BIP "functorial Rees algebra map"]
def map {I : Ideal R} {S : Type*} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) : reesAlgebra I →+* reesAlgebra J :=
  RingHom.codRestrict
    ((Polynomial.mapRingHom f).comp (reesAlgebra I).toSubring.subtype)
    (reesAlgebra J).toSubring
    (map_mem f hIJ)

/-- The polynomial underlying `map f hIJ x` is obtained by mapping
the coefficients of `x` along `f`. -/
@[stacks 0BIP "Rees algebra map evaluation", simp]
theorem map_apply {I : Ideal R} {S : Type*} [CommRing S] {J : Ideal S}
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (x : reesAlgebra I) :
    (map f hIJ x).1 = Polynomial.map f x.1 := sorry

/-- A Rees-algebra map induced by an inclusion of centers preserves every homogeneous
component. -/
@[stacks 0BIP "Rees algebra map graded membership"]
theorem map_mem_grade
    {S : Type*} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I ≤ Ideal.comap f J)
    {n : ℕ} {x : reesAlgebra I} (hx : x ∈ grade I n) :
    map f hIJ x ∈ grade J n := sorry

/-- The graded Rees-algebra map induced by a ring map carrying one center into another. -/
@[stacks 0BIP "functorial Rees grading map"]
noncomputable def gradedMap
    {S : Type*} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I ≤ Ideal.comap f J) :
    grade I →+*ᵍ grade J where
  toRingHom := map f hIJ
  map_mem := map_mem_grade f I J hIJ

/-- A graded Rees map sends a distinguished degree-one element to a compatible target element. -/
@[stacks 0BIP "graded Rees map degree-one compatibility"]
theorem gradedMap_degreeOne
    {S : Type*} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I ≤ Ideal.comap f J)
    (a : I) (b : J) (hab : f a = b) :
    gradedMap f I J (hIJ := hIJ) (degreeOne I a) =
      degreeOne J b := sorry

/-- Scalars of `reesAlgebra I` belong to its degree-zero homogeneous piece. -/
@[stacks 052Q "degree-zero Rees scalar membership"]
theorem algebraMap_mem_zero (r : R) :
    algebraMap R (reesAlgebra I) r ∈ grade I 0 := sorry

/-- The value of the degree-zero Rees map on a scalar. -/
noncomputable def zeroAlgebraMapToFun (r : R) : grade I 0 :=
  ⟨algebraMap R (reesAlgebra I) r, algebraMap_mem_zero I r⟩

/-- The degree-zero Rees map sends one to one. -/
theorem zeroAlgebraMapToFun_one : zeroAlgebraMapToFun I 1 = 1 := sorry

/-- The degree-zero Rees map preserves multiplication. -/
theorem zeroAlgebraMapToFun_mul (x y : R) :
    zeroAlgebraMapToFun I (x * y) = zeroAlgebraMapToFun I x * zeroAlgebraMapToFun I y := sorry

/-- The degree-zero Rees map sends zero to zero. -/
theorem zeroAlgebraMapToFun_zero : zeroAlgebraMapToFun I 0 = 0 := sorry

/-- The degree-zero Rees map preserves addition. -/
theorem zeroAlgebraMapToFun_add (x y : R) :
    zeroAlgebraMapToFun I (x + y) = zeroAlgebraMapToFun I x + zeroAlgebraMapToFun I y := sorry

/-- The canonical ring homomorphism from `R` to the degree-zero Rees piece. -/
@[stacks 052Q "degree-zero Rees algebra map"]
noncomputable def zeroAlgebraMap : R →+* grade I 0 :=
  algebraMap R (grade I 0)

end

end ReesAlgebra.Grading
