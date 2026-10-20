module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

universe u

open scoped TensorProduct

namespace MvPolynomial

/-- For a field `k`, tensoring the inclusion of the variable ideal in
`MvPolynomial (Fin 2) k` with that ideal does not preserve injectivity. -/
theorem idealOfVars_subtype_rTensor_idealOfVars_not_injective (k : Type u) [Field k] :
    ¬ Function.Injective
      ((idealOfVars (Fin 2) k).subtype.rTensor (idealOfVars (Fin 2) k)) := sorry

/-- For a field `k`, tensoring the inclusion of the variable ideal in
`MvPolynomial (Fin 2) k` with its quotient does not preserve injectivity. -/
theorem idealOfVars_subtype_rTensor_quotient_not_injective (k : Type u) [Field k] :
    ¬ Function.Injective
      ((idealOfVars (Fin 2) k).subtype.rTensor
        (MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k)) := sorry

/-- The ideal of variables in `MvPolynomial (Fin 2) k` is not a flat module
over the polynomial ring when `k` is a field. -/
theorem not_flat_idealOfVars (k : Type u) [Field k] :
    ¬ Module.Flat (MvPolynomial (Fin 2) k) (idealOfVars (Fin 2) k) := sorry

/-- The quotient of `MvPolynomial (Fin 2) k` by its ideal of variables is not
a flat module over the polynomial ring when `k` is a field. -/
theorem not_flat_quotient_idealOfVars (k : Type u) [Field k] :
    ¬ Module.Flat (MvPolynomial (Fin 2) k)
        (MvPolynomial (Fin 2) k ⧸ idealOfVars (Fin 2) k) := sorry

end MvPolynomial
