module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product.Counterexample

/-!
# The complex base change of `Spec(ℚ(i))`

This file identifies the complex base change of the concrete affine scheme
`Spec(ℚ(i))` with two copies of `Spec(ℂ)` and records the resulting failure of
geometric connectedness over `ℚ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits CommRingCat
open scoped TensorProduct

namespace AlgebraicGeometry.RatSqrtNegOne

/-- The complex base change of the structure morphism `Spec(ℚ(i)) ⟶ Spec(ℚ)`. -/
abbrev complexBaseChange : Scheme :=
  pullback ratSqrtNegOneToSpecRat (Spec.map (ofHom (algebraMap ℚ ℂ)))

/-- The tensor-product ring `ℂ ⊗[ℚ] ℚ(i)`. -/
abbrev complexTensor : Type :=
  ℂ ⊗[ℚ] ratSqrtNegOne

/-- The affine scheme with coordinate ring `ℂ ⊗[ℚ] ℚ(i)`. -/
abbrev complexTensorSpec : Scheme :=
  Spec (.of complexTensor)

/-- The polynomial `X ^ 2 + 1` defining `ℚ(i)` vanishes at `I : ℂ`. -/
theorem polynomialAevalI :
    Polynomial.eval₂ (algebraMap ℚ ℂ) Complex.I ratSqrtNegOnePolynomial = 0 := sorry

/-- The polynomial `X ^ 2 + 1` defining `ℚ(i)` vanishes at `-I : ℂ`. -/
theorem polynomialAevalNegI :
    Polynomial.eval₂ (algebraMap ℚ ℂ) (-Complex.I) ratSqrtNegOnePolynomial = 0 := sorry

/-- The `ℚ`-algebra embedding `ℚ(i) ⟶ ℂ` that sends the adjoined root to `I`. -/
noncomputable def toComplexI : ratSqrtNegOne →ₐ[ℚ] ℂ :=
  AdjoinRoot.liftAlgHom ratSqrtNegOnePolynomial (Algebra.ofId ℚ ℂ) Complex.I polynomialAevalI

/-- The `ℚ`-algebra embedding `ℚ(i) ⟶ ℂ` that sends the adjoined root to `-I`. -/
noncomputable def toComplexNegI : ratSqrtNegOne →ₐ[ℚ] ℂ :=
  AdjoinRoot.liftAlgHom ratSqrtNegOnePolynomial (Algebra.ofId ℚ ℂ) (-Complex.I)
    polynomialAevalNegI

/-- The pair of complex embeddings `ℚ(i) ⟶ ℂ × ℂ` obtained from the two roots of
`X ^ 2 + 1`. -/
noncomputable def toComplexProd : ratSqrtNegOne →ₐ[ℚ] ℂ × ℂ :=
  toComplexI.prod toComplexNegI

/-- The complex base change of `Spec(ℚ(i))` is the spectrum of `ℂ ⊗[ℚ] ℚ(i)`. -/
noncomputable def complexBaseChangeIsoSpec :
    complexBaseChange ≅ complexTensorSpec :=
  pullbackSpecIso ℚ ratSqrtNegOne ℂ ≪≫
    Scheme.Spec.mapIso
      (Algebra.TensorProduct.comm ℚ ratSqrtNegOne ℂ).symm.toRingEquiv.toCommRingCatIso.op

/-- The tensor-product ring `ℂ ⊗[ℚ] ℚ(i)` splits as `ℂ × ℂ`. -/
noncomputable def complexTensorEquivProd : complexTensor ≃+* (ℂ × ℂ) where
  toFun := Algebra.TensorProduct.productMap
    ((AlgHom.id ℚ ℂ).prod (AlgHom.id ℚ ℂ)) toComplexProd
  invFun := fun z ↦
    (((z.1 + z.2) / (2 : ℂ)) ⊗ₜ[ℚ] (1 : ratSqrtNegOne)) +
      (((z.1 - z.2) / ((2 : ℂ) * Complex.I)) ⊗ₜ[ℚ]
        AdjoinRoot.root ratSqrtNegOnePolynomial)
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry

/-- The complex base change of `Spec(ℚ(i))` is isomorphic to the coproduct of two copies of
`Spec(ℂ)`. -/
noncomputable def complexBaseChangeIsoCoprod :
    complexBaseChange ≅ Spec (.of ℂ) ⨿ Spec (.of ℂ) :=
  complexBaseChangeIsoSpec ≪≫
    Scheme.Spec.mapIso complexTensorEquivProd.symm.toCommRingCatIso.op ≪≫
      (asIso (coprodSpec ℂ ℂ)).symm

/-- The complex base change of `Spec(ℚ(i))` has disconnected underlying space. -/
theorem complexBaseChangeNotConnected :
    ¬ ConnectedSpace complexBaseChange := sorry

/-- The structure morphism `Spec(ℚ(i)) ⟶ Spec(ℚ)` is not geometrically connected. -/
theorem notGeometricallyConnected :
    ¬ GeometricallyConnected ratSqrtNegOneToSpecRat := sorry

end AlgebraicGeometry.RatSqrtNegOne
