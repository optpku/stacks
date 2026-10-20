module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Presentation.Jacobian.Fin

/-!
# Jacobian annihilation for the naive cotangent object

The leading Jacobian minor of a finite presentation annihilates Ext¹ of the
derived naive cotangent object, and acts by zero on that object for a square
presentation.
-/

@[expose] public section

open CategoryTheory
open scoped DerivedExt

universe u v

namespace Algebra.Presentation

/-- The leading Jacobian determinant annihilates Ext¹ of the naive cotangent object
for every module over a finite presentation with at most as many relations as variables. -/
theorem leadingJacobianDet_annihilates_extOne_naiveCotangent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (P : Presentation A B (Fin n) (Fin m)) (hmn : m ≤ n) :
    twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject A B)
      (Ideal.span {algebraMap P.Ring B (P.leadingJacobianDet hmn le_rfl)}) := sorry

/-- For a square finite presentation, scalar multiplication by the leading Jacobian
determinant is zero on the naive cotangent object in the derived category. -/
theorem leadingJacobianDet_smul_id_naiveCotangentObject_eq_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : Presentation A B (Fin n) (Fin n)) :
    algebraMap P.Ring B (P.leadingJacobianDet le_rfl le_rfl) •
      𝟙 (naiveCotangentObject A B) = 0 := sorry

/-- The leading Jacobian determinant belongs to the annihilator of Ext¹ of the
naive cotangent object with coefficients in any module. -/
theorem leadingJacobianDet_mem_annihilator_extOne_naiveCotangent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n m : ℕ} (P : Presentation A B (Fin n) (Fin m)) (hmn : m ≤ n)
    (N : ModuleCat B) :
    algebraMap P.Ring B (P.leadingJacobianDet hmn le_rfl) ∈
      Module.annihilator B
        ((DerivedCategory.Ext.moduleFunctor (naiveCotangentObject A B)
            (1 : ℤ)).obj N) := sorry

end Algebra.Presentation
