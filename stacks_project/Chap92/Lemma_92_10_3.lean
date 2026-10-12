/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_10_2
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of the cotangent complex for perfect rings

In characteristic `p`, if `A` and `B` are perfect then the André-Quillen complex
`L_{B/A}` is the zero object of `D(B)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Algebra.CotangentComplex.Frobenius

/-- Lemma 92.10.3. Let `p` be a prime number. Let `A ⟶ B` be a ring homomorphism and
assume that `p = 0` in `A`. If `A` and `B` are perfect, then `L_{B/A}` is zero in
`D(B)`. -/
@[stacks 0G60]
theorem cotangentComplex_isZero (p : ℕ) [Fact p.Prime] {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) (hp : (p : A) = 0)
    [PerfectRing A p] [PerfectRing B p] :
    IsZero (DerivedCategory.Q.obj (RingHom.cotangentComplex f)) :=
  sorry

/-- The André-Quillen cotangent complex of a perfect algebra over a perfect ring
vanishes in the derived category when `p = 0` in the base. -/
theorem derived_isZero (p : ℕ) [Fact p.Prime] (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] (hp : (p : A) = 0)
    [PerfectRing A p] [PerfectRing B p] :
    IsZero (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) :=
  sorry

end Algebra.CotangentComplex.Frobenius
