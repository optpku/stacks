module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.DividedPowers.Differential

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape ModuleCat MonoidalCategory TensorProduct

universe u

namespace DPPolynomial.DeRham

variable (A : Type u) [CommRing A] (ι : Type u)

/-- The unaugmented divided-power de Rham complex of the indexed polynomial algebra. -/
noncomputable def complex : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (form A ι) (formDifferential A ι) (fun _ ↦ by sorry)

/-- The degree-`n` object of the divided-power de Rham complex. -/
theorem complex_X (n : ℕ) : (complex A ι).X n = form A ι n := sorry

/-- The degree-`n` differential of the divided-power de Rham complex. -/
theorem complex_d (n : ℕ) :
    (complex A ι).d n (n + 1) = formDifferential A ι n := sorry

/-- The coefficient term in degree zero or positive degree of the divided-power de Rham complex. -/
noncomputable def coefficientTerm (M : Type u) [AddCommGroup M] [Module A M] :
    ℕ → ModuleCat.{u} A
  | 0 => ModuleCat.of A M
  | n + 1 => (tensorLeft (ModuleCat.of A M)).obj (form A ι n)

/-- The degree-zero unit form of the divided-power polynomial algebra. -/
noncomputable def formUnit : form A ι 0 :=
  (dividedPowerRelation A ι 0).mkQ
    (KaehlerDifferential.DeRham.aExact A (DPPolynomial A ι) 0 Fin.elim0)

/-- The augmentation from coefficients into degree-zero coefficient forms. -/
noncomputable def augmentation (M : Type u) [AddCommGroup M] [Module A M] :
    coefficientTerm A ι M 0 ⟶ coefficientTerm A ι M 1 :=
  ModuleCat.ofHom
    { toFun := fun m => TensorProduct.tmul A m (formUnit A ι)
      map_add' := by sorry
      map_smul' := by sorry }

/-- The augmentation sends a coefficient to its tensor with the unit form. -/
theorem augmentation_apply (M : Type u) [AddCommGroup M] [Module A M] (m : M) :
    (augmentation A ι M).hom m = TensorProduct.tmul A m (formUnit A ι) := sorry

/-- The differentials in the augmented coefficient complex. -/
noncomputable def coefficientDifferential (M : Type u) [AddCommGroup M] [Module A M] :
    (n : ℕ) → coefficientTerm A ι M n ⟶ coefficientTerm A ι M (n + 1)
  | 0 => augmentation A ι M
  | n + 1 => (tensorLeft (ModuleCat.of A M)).map (formDifferential A ι n)

/-- The augmented divided-power de Rham complex with coefficients in `M`. -/
noncomputable def coefficientComplex (M : Type u) [AddCommGroup M] [Module A M] :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (coefficientTerm A ι M) (coefficientDifferential A ι M) (fun _ ↦ by sorry)

/-- The degree-zero coefficient term is `M`. -/
theorem coefficientComplex_X_zero (M : Type u) [AddCommGroup M] [Module A M] :
    (coefficientComplex A ι M).X 0 = ModuleCat.of A M := sorry

/-- The positive-degree coefficient term is the tensor product with divided-power forms. -/
theorem coefficientComplex_X_succ (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ) :
    (coefficientComplex A ι M).X (n + 1) =
      (tensorLeft (ModuleCat.of A M)).obj (form A ι n) := sorry

/-- The degree-zero coefficient differential is the augmentation. -/
theorem coefficientComplex_d_zero (M : Type u) [AddCommGroup M] [Module A M] :
    (coefficientComplex A ι M).d 0 1 = augmentation A ι M := sorry

/-- The augmented divided-power de Rham coefficient complex is acyclic for every module. -/
theorem coefficientComplex_acyclic (M : Type u) [AddCommGroup M] [Module A M] :
    (coefficientComplex A ι M).Acyclic := sorry

end DPPolynomial.DeRham
