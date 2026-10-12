/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Presentation.Jacobian.Fin

/-!
# Jacobian annihilation for the naive cotangent complex

The leading Jacobian minor of a finite presentation annihilates Ext¹ of the
derived naive cotangent object, and kills that object in `D(B)` when the
presentation is square.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedExt

universe u v

namespace Algebra.Presentation

/-- Lemma 88.7.1 (1): for a presentation `P` of `B` over `A` on `n` variables and
`m` relations with `m ≤ n`, the image in `B` of the leading `m × m` Jacobian
determinant annihilates `Ext¹_B(NL{B⁄A}, N)` for every `B`-module `N`. -/
@[stacks 0GAV]
theorem leadingJacobianDet_annihilates_extOne_naiveCotangent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (P : Presentation A B (Fin n) (Fin m)) (hmn : m ≤ n) :
    twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject A B)
      (Ideal.span {algebraMap P.Ring B (P.leadingJacobianDet hmn le_rfl)}) := sorry

/-- Lemma 88.7.1 (2): if `n = m`, then multiplication by the leading Jacobian
determinant is zero on `NL{B⁄A}` in `D(B)`. -/
@[stacks 0GAV]
theorem leadingJacobianDet_smul_id_naiveCotangentObject_eq_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : Presentation A B (Fin n) (Fin n)) :
    algebraMap P.Ring B (P.leadingJacobianDet le_rfl le_rfl) •
      𝟙 (naiveCotangentObject A B) = 0 := sorry

/-- The image of the leading Jacobian determinant lies in the annihilator of
`Ext¹_B(NL{B⁄A}, N)` for every `B`-module `N`. -/
theorem leadingJacobianDet_mem_annihilator_extOne_naiveCotangent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (P : Presentation A B (Fin n) (Fin m)) (hmn : m ≤ n)
    (N : ModuleCat B) :
    algebraMap P.Ring B (P.leadingJacobianDet hmn le_rfl) ∈
      Module.annihilator B
        ((DerivedCategory.Ext.moduleFunctor (naiveCotangentObject A B)
            (1 : ℤ)).obj N) := sorry

end Algebra.Presentation
