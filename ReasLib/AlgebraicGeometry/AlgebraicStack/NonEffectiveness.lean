/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Triangle
public import ReasLib.Algebra.Category.CommRingCat.IdealPower
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Quotient
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.FieldTheory.AlgebraicClosure.FiniteField

/-!
# Non-effective formal systems on classifying stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.StrongEffectiveness

/-- Over an algebraically closed field that is not an algebraic closure of a finite
field, the classifying stack of a nonzero abelian variety admits a non-effective
formal object system over the positive powers of the triangle ideal, with the
given field as coefficient ring. -/
theorem exists_not_isEffective_of_triangle {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] (hA : ¬ IsIso A.hom) :
    ∃ ξ : FormalObjectSystem (AlgebraicStack.classifying (Grp.mk A)).p,
      ξ.ringSystem = CommRingCat.IdealPower.Positive.system (MvPolynomial.Triangle.ideal k) ∧
        ξ.coeffRing = CommRingCat.of k ∧ ¬ ξ.IsEffective := sorry

/-- Over an algebraically closed field that is not an algebraic closure of a finite
field, the classifying stack of a nonzero abelian variety admits a non-effective
formal object system. -/
theorem exists_not_isEffective {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] (hA : ¬ IsIso A.hom) :
    ∃ ξ : FormalObjectSystem (AlgebraicStack.classifying (Grp.mk A)).p,
      ¬ ξ.IsEffective := by
  obtain ⟨ξ, _, _, hξ⟩ := exists_not_isEffective_of_triangle hk A hA
  exact ⟨ξ, hξ⟩

end AlgebraicGeometry.GroupoidsOver.StrongEffectiveness
