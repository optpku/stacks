/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.RingTheory.Seminormal.Perfect

/-!
# Frobenius colimits of rings

This module constructs the sequential colimit of a commutative `ZMod p`-algebra under
Frobenius, together with its canonical maps and ring-theoretic properties.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Ring.FrobeniusColimit

/-- A prime `p` acts by zero on every commutative `ZMod p`-algebra. -/
theorem primeCast_eq_zero (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : (p : A) = 0 := sorry

/-- The Frobenius endomorphism of a commutative `ZMod p`-algebra. -/
def frobenius (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : A →+* A :=
  RingHom.frobeniusOfPrime p (primeCast_eq_zero p A)

/-- Frobenius sends an element to its `p`-th power. -/
theorem frobenius_apply (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (x : A) :
    frobenius p A x = x ^ p := sorry

/-- The sequential diagram consisting of copies of `A` joined by Frobenius. -/
def diagram (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (fun _ : ℕ ↦
    (CommRingCat.ofHom (frobenius p A) : CommRingCat.of A ⟶ CommRingCat.of A))

/-- Every object of the Frobenius diagram is the original commutative ring. -/
theorem diagram_obj (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    (diagram p A).obj n = CommRingCat.of A := sorry

/-- Every successor map in the sequential diagram is Frobenius. -/
theorem diagram_map_succ (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    (diagram p A).map (homOfLE n.le_succ) = CommRingCat.ofHom (frobenius p A) := sorry

/-- The colimit of a commutative `ZMod p`-algebra under repeated Frobenius. -/
noncomputable def ring (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : CommRingCat.{u} :=
  colimit (diagram p A)

/-- The canonical morphism from the `n`-th Frobenius stage to the colimit. -/
noncomputable def ι (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    CommRingCat.of A ⟶ ring p A :=
  colimit.ι (diagram p A) n

/-- Successive canonical stage maps are compatible with Frobenius. -/
theorem ι_succ (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] (n : ℕ) :
    CommRingCat.ofHom (frobenius p A) ≫ ι p A (n + 1) = ι p A n := sorry

/-- The underlying ring homomorphism from the initial stage to the Frobenius colimit. -/
noncomputable def toRingHom (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : A →+* ring p A :=
  (ι p A 0).hom

/-- The initial-stage map equips the Frobenius colimit with its canonical `A`-algebra structure. -/
noncomputable instance instAlgebra (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : Algebra A (ring p A) :=
  (toRingHom p A).toAlgebra

/-- The algebra map into the Frobenius colimit is its initial-stage ring homomorphism. -/
theorem algebraMap_eq_toRingHom (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    algebraMap A (ring p A) = toRingHom p A := sorry

/-- The sequential Frobenius colimit is perfect. -/
noncomputable instance instPerfectRing (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] : PerfectRing (ring p A) p := sorry

/-- The sequential Frobenius colimit is absolutely weakly normal. -/
noncomputable instance instAbsolutelyWeaklyNormalRing (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Algebra (ZMod p) A] :
    AbsolutelyWeaklyNormalRing (ring p A) := sorry

end Ring.FrobeniusColimit
