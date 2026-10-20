module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Concentrated

/-!
# Ordinary Algebras as Differential Graded Algebras

An ordinary algebra has a canonical cochain-DGA model supported in degree zero.  The underlying
complex is mathlib's single-term complex; the multiplication and unit are transported through
its canonical degree-zero identification.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex

namespace CochainDGAlgebra

variable (R : Type u) [CommRing R]
variable (A : Type v) [Ring A] [Algebra R A]

/-- The single-term cochain complex underlying an ordinary algebra regarded as a DGA. -/
noncomputable abbrev degreeZeroComplex : CochainComplex (ModuleCat.{v} R) ℤ :=
  (single (ModuleCat.{v} R) (up ℤ) 0).obj (ModuleCat.of R A)

/-- The canonical identification between degree zero of `degreeZeroComplex R A` and `A`. -/
noncomputable def degreeZeroIso : (degreeZeroComplex R A).X 0 ≅ ModuleCat.of R A :=
  singleObjXSelf (up ℤ) 0 (ModuleCat.of R A)

/-- Multiplication on the degree-zero component of the single-term complex. -/
noncomputable def degreeZeroMulZero :
    (degreeZeroComplex R A).X 0 →ₗ[R]
      (degreeZeroComplex R A).X 0 →ₗ[R] (degreeZeroComplex R A).X 0 where
  toFun x :=
    { toFun := fun y ↦ (degreeZeroIso R A).inv ((degreeZeroIso R A).hom x *
        (degreeZeroIso R A).hom y)
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Homogeneous multiplication for the degree-zero DGA of an ordinary algebra. -/
noncomputable def degreeZeroMul : (i j : ℤ) →
    (degreeZeroComplex R A).X i →ₗ[R]
      (degreeZeroComplex R A).X j →ₗ[R] (degreeZeroComplex R A).X (i + j)
  | 0, 0 => degreeZeroMulZero R A
  | _, _ => 0

/-- An ordinary `R`-algebra, regarded canonically as a cochain DGA supported in degree zero. -/
@[stacks 09SC "ordinary algebra as a degree-zero differential graded algebra"]
noncomputable def ofAlgebra : CochainDGAlgebra.{u, v} R where
  toCochainComplex := degreeZeroComplex R A
  mul := degreeZeroMul R A
  one := (degreeZeroIso R A).inv (1 : A)
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  leibniz := sorry

/-- The degree-zero component of `ofAlgebra R A` is canonically the ordinary algebra `A`. -/
noncomputable def ofAlgebraZeroIso : (ofAlgebra R A).X 0 ≅ ModuleCat.of R A :=
  degreeZeroIso R A

/-- The DGA attached to an ordinary algebra is concentrated in degree zero. -/
theorem ofAlgebra_isConcentratedInDegreeZero :
    (ofAlgebra R A).IsConcentratedInDegreeZero := sorry

end CochainDGAlgebra
