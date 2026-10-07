module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Diagonal
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor

/-!
# Hochschild Cohomology of a Differential Graded Algebra

Hochschild cohomology with coefficients is the shifted Hom from the diagonal bimodule in the
derived category of bimodules.  This formulation keeps coefficients primary and makes
invariance under a diagonal-preserving equivalence a direct specialization of shifted-Hom
transport.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainDGAlgebra.Hochschild

variable {R : Type u} [CommRing R]

/-- Hochschild cohomology of a DGA `A` with coefficients in a derived `(A, A)`-bimodule `M`:
`Extⁿ_{Aᵉ}(A, M)`. -/
@[stacks 09ST "Hochschild cohomology with coefficients"]
abbrev CohomologyWith (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedBimodule.Derived.Category.{u, v, v, v} A A) (n : ℤ) :=
  ShiftedHom (DifferentialGradedBimodule.Derived.diagonalObject A) M n

/-- Hochschild cohomology of a DGA, using the diagonal bimodule as coefficients. -/
@[stacks 09ST "Hochschild cohomology of a differential graded algebra"]
abbrev Cohomology (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :=
  CohomologyWith A (DifferentialGradedBimodule.Derived.diagonalObject A) n

/-- An additive, linear, shift-compatible equivalence of bimodule-derived categories transports
Hochschild cohomology with coefficients once the diagonal and coefficient objects are
identified. -/
@[stacks 09ST "Hochschild cohomology comparison under a bimodule equivalence"]
noncomputable def linearEquivWith {A B : CochainDGAlgebra.{u, v} R}
    (e : DifferentialGradedBimodule.Derived.Category A A ≌
      DifferentialGradedBimodule.Derived.Category B B)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {M : DifferentialGradedBimodule.Derived.Category A A}
    {N : DifferentialGradedBimodule.Derived.Category B B}
    (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
      DifferentialGradedBimodule.Derived.diagonalObject B)
    (hM : e.functor.obj M ≅ N) (n : ℤ) :
    CohomologyWith A M n ≃ₗ[R] CohomologyWith B N n :=
  e.shiftedHomLinearEquiv hΔ hM n

/-- The Hochschild cohomology equivalence with coefficients is the shifted image conjugated by
the chosen diagonal and coefficient identifications. -/
@[simp]
theorem linearEquivWith_apply {A B : CochainDGAlgebra.{u, v} R}
    (e : DifferentialGradedBimodule.Derived.Category A A ≌
      DifferentialGradedBimodule.Derived.Category B B)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {M : DifferentialGradedBimodule.Derived.Category A A}
    {N : DifferentialGradedBimodule.Derived.Category B B}
    (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
      DifferentialGradedBimodule.Derived.diagonalObject B)
    (hM : e.functor.obj M ≅ N) (n : ℤ) (f : CohomologyWith A M n) :
    linearEquivWith e hΔ hM n f =
      hΔ.inv ≫ ShiftedHom.map f e.functor ≫
        (shiftFunctor (DifferentialGradedBimodule.Derived.Category B B) n).map hM.hom := sorry

/-- The inverse Hochschild cohomology equivalence with coefficients is the explicit transport
along the chosen quasi-inverse and the pulled-back endpoint identifications. -/
@[simp]
theorem linearEquivWith_symm_apply {A B : CochainDGAlgebra.{u, v} R}
    (e : DifferentialGradedBimodule.Derived.Category A A ≌
      DifferentialGradedBimodule.Derived.Category B B)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {M : DifferentialGradedBimodule.Derived.Category A A}
    {N : DifferentialGradedBimodule.Derived.Category B B}
    (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
      DifferentialGradedBimodule.Derived.diagonalObject B)
    (hM : e.functor.obj M ≅ N) (n : ℤ) (f : CohomologyWith B N n) :
    (linearEquivWith e hΔ hM n).symm f =
      e.shiftedHomInverseMap hΔ hM n f := sorry

/-- Remark 22.37.10 (09ST): an additive, linear, shift-compatible equivalence of bimodule-derived
categories that identifies the diagonal objects induces a linear equivalence on Hochschild
cohomology in every degree. -/
@[stacks 09ST "Hochschild cohomology under a derived equivalence"]
noncomputable def linearEquiv {A B : CochainDGAlgebra.{u, v} R}
    (e : DifferentialGradedBimodule.Derived.Category A A ≌
      DifferentialGradedBimodule.Derived.Category B B)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
      DifferentialGradedBimodule.Derived.diagonalObject B)
    (n : ℤ) : Cohomology A n ≃ₗ[R] Cohomology B n :=
  linearEquivWith e hΔ hΔ n

/-- The Hochschild cohomology equivalence acts by the shifted image conjugated by the diagonal
identification. -/
@[simp]
theorem linearEquiv_apply {A B : CochainDGAlgebra.{u, v} R}
    (e : DifferentialGradedBimodule.Derived.Category A A ≌
      DifferentialGradedBimodule.Derived.Category B B)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
      DifferentialGradedBimodule.Derived.diagonalObject B)
    (n : ℤ) (f : Cohomology A n) :
    linearEquiv e hΔ n f =
      hΔ.inv ≫ ShiftedHom.map f e.functor ≫
        (shiftFunctor (DifferentialGradedBimodule.Derived.Category B B) n).map hΔ.hom := sorry

/-- The inverse Hochschild cohomology equivalence is the explicit shifted-Hom transport along
the chosen quasi-inverse. -/
@[simp]
theorem linearEquiv_symm_apply {A B : CochainDGAlgebra.{u, v} R}
    (e : DifferentialGradedBimodule.Derived.Category A A ≌
      DifferentialGradedBimodule.Derived.Category B B)
    [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    (hΔ : e.functor.obj (DifferentialGradedBimodule.Derived.diagonalObject A) ≅
      DifferentialGradedBimodule.Derived.diagonalObject B)
    (n : ℤ) (f : Cohomology B n) :
    (linearEquiv e hΔ n).symm f =
      e.shiftedHomInverseMap hΔ hΔ n f := sorry

end CochainDGAlgebra.Hochschild
