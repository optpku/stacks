/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Projective
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AbelianVariety CategoryTheory.MonObj

universe u

/- Proposition 39.9.11 (1): an abelian variety is projective over its base field. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.instProjective :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A],
      AlgebraicGeometry.Projective A.hom)

/- Proposition 39.9.11 (2): an abelian variety is a commutative group scheme. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.instIsCommMonObj :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A],
      CategoryTheory.IsCommMonObj A)

/- Proposition 39.9.11 (3): multiplication by a positive integer on an abelian variety is
surjective. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.instMulBySurjective :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A]
      (n : ℕ) [NeZero n], AlgebraicGeometry.Surjective ([n]ₐ A))

/- Proposition 39.9.11 (4): over an algebraically closed field, multiplication by a positive
integer is surjective on the group of rational points. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.rationalPoints_nsmul_surjective :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A] [IsAlgClosed k]
      (n : ℕ), 1 ≤ n → Function.Surjective
        (fun x : AlgebraicGeometry.SchemeOverField.rationalPoints A ↦ n • x))

/- Proposition 39.9.11 (5): the `n`-torsion group scheme is finite locally free of degree
`n ^ (2 * dimension A)` over the base field. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.instTorsionFiniteLocallyFreeOfRank :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A]
      (n : ℕ) [NeZero n],
      AlgebraicGeometry.IsFiniteLocallyFreeOfRank
        (AlgebraicGeometry.SchemeOverField.torsionGroupScheme A n).X.hom
        (n ^ (2 * AlgebraicGeometry.AbelianVariety.dimension A)))

/- Proposition 39.9.11 (6), with the positive-dimensional hypothesis required by
Lemma 39.9.9: the `n`-torsion group scheme is étale exactly when `n` is invertible in
the base field. The hypothesis excludes the zero-dimensional trivial abelian variety. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.torsion_etale_iff :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A],
      0 < AlgebraicGeometry.AbelianVariety.dimension A → ∀ (n : ℕ) [NeZero n],
        AlgebraicGeometry.Etale
            (AlgebraicGeometry.SchemeOverField.torsionGroupScheme A n).X.hom ↔
          IsUnit (n : k))

/- Proposition 39.9.11 (7): prime-to-characteristic rational `n`-torsion over an algebraically
closed field is a product of `2 * dimension A` copies of `ZMod n`. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.rationalTorsion_equiv :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A] [IsAlgClosed k]
      (n : ℕ) [NeZero n], IsUnit (n : k) →
        Nonempty
          (AddSubgroup.torsionBy
              (AlgebraicGeometry.SchemeOverField.rationalPoints A) (n : ℤ) ≃+
            (Fin (2 * AlgebraicGeometry.AbelianVariety.dimension A) → ZMod n)))

/- Proposition 39.9.11 (8): in prime characteristic `p`, rational `p ^ m`-torsion has a fixed
rank at most `dimension A`. -/
@[stacks 03RP] #check
  (AlgebraicGeometry.AbelianVariety.exists_pRank :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A] [IsAlgClosed k]
      (p : ℕ) [Fact p.Prime] [CharP k p],
      ∃ f : ℕ, f ≤ AlgebraicGeometry.AbelianVariety.dimension A ∧ ∀ m : ℕ, 1 ≤ m →
        Nonempty
          (AddSubgroup.torsionBy
              (AlgebraicGeometry.SchemeOverField.rationalPoints A) ((p ^ m : ℕ) : ℤ) ≃+
            (Fin f → ZMod (p ^ m))))
