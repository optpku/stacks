module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# A product of varieties over a non-algebraically-closed field

This file gives the concrete splitting of the self-fibre product of
`Spec(ℚ(i))` over `Spec(ℚ)` and records its failure to be a variety.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits CommRingCat
open scoped Polynomial TensorProduct

namespace AlgebraicGeometry

/-- The quadratic polynomial cutting out the affine `ℚ`-scheme `Spec(ℚ(i))`. -/
abbrev ratSqrtNegOnePolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 + 1

/-- A concrete model for `ℚ(i)` as `ℚ[X] / (X ^ 2 + 1)`. -/
abbrev ratSqrtNegOne : Type :=
  AdjoinRoot ratSqrtNegOnePolynomial

/-- The affine scheme `Spec(ℚ(i))`. -/
abbrev ratSqrtNegOneSpec : Scheme :=
  Spec (CommRingCat.of ratSqrtNegOne)

/-- The structure morphism `Spec(ℚ(i)) ⟶ Spec(ℚ)`. -/
abbrev ratSqrtNegOneToSpecRat :
    ratSqrtNegOneSpec ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (ofHom (algebraMap ℚ ratSqrtNegOne))

/-- The affine scheme `Spec(ℚ(i))`, viewed as an object over `Spec(ℚ)`. -/
abbrev ratSqrtNegOneOverRat : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk ratSqrtNegOneToSpecRat

/-- The affine `ℚ`-scheme `Spec(ℚ(i))` is a variety over `Spec(ℚ)`. -/
instance ratSqrtNegOneOverRatVariety :
    Variety ratSqrtNegOneOverRat := sorry

/-- The self-fibre product `Spec(ℚ(i)) ×[Spec(ℚ)] Spec(ℚ(i))`. -/
abbrev ratSqrtNegOneSelfFiberProduct : Scheme :=
  pullback ratSqrtNegOneToSpecRat ratSqrtNegOneToSpecRat

/-- The self-fibre product of `Spec(ℚ(i))` over `Spec(ℚ)`, viewed over `Spec(ℚ)` through the
first projection. -/
abbrev ratSqrtNegOneSelfFiberProductOverRat :
    Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk
    (pullback.fst ratSqrtNegOneToSpecRat ratSqrtNegOneToSpecRat ≫ ratSqrtNegOneToSpecRat)

/-- The affine tensor-product model `Spec (ℚ(i) ⊗[ℚ] ℚ(i))` of the self-fibre product. -/
abbrev ratSqrtNegOneTensorSelfSpec : Scheme :=
  Spec (CommRingCat.of <| ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne)

/-- The polynomial `X ^ 2 + 1` vanishes at the negative of its adjoined root. -/
theorem ratSqrtNegOnePolynomial_aeval_negRoot :
    Polynomial.eval₂ (algebraMap ℚ ratSqrtNegOne)
      (-AdjoinRoot.root ratSqrtNegOnePolynomial) ratSqrtNegOnePolynomial = 0 := sorry

/-- The conjugation automorphism of `ℚ(i)` sending the adjoined root to its negative. -/
noncomputable def ratSqrtNegOneConj : ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne :=
  AdjoinRoot.liftAlgHom ratSqrtNegOnePolynomial (Algebra.ofId ℚ ratSqrtNegOne)
    (-AdjoinRoot.root ratSqrtNegOnePolynomial) ratSqrtNegOnePolynomial_aeval_negRoot

/-- The diagonal `ℚ`-algebra map `ℚ(i) ⟶ ℚ(i) × ℚ(i)`. -/
noncomputable def ratSqrtNegOneToProdDiagonal :
    ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne × ratSqrtNegOne :=
  (AlgHom.id ℚ ratSqrtNegOne).prod (AlgHom.id ℚ ratSqrtNegOne)

/-- The pair of embeddings `ℚ(i) ⟶ ℚ(i) × ℚ(i)` given by identity and conjugation. -/
noncomputable def ratSqrtNegOneToProdPair :
    ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne × ratSqrtNegOne :=
  (AlgHom.id ℚ ratSqrtNegOne).prod ratSqrtNegOneConj

/-- The `ℚ`-algebra map `ℚ(i) ⊗[ℚ] ℚ(i) ⟶ ℚ(i) × ℚ(i)` induced by identity and
conjugation. -/
noncomputable def ratSqrtNegOneTensorSelfToProd :
    ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne →ₐ[ℚ] ratSqrtNegOne × ratSqrtNegOne :=
  Algebra.TensorProduct.productMap ratSqrtNegOneToProdDiagonal ratSqrtNegOneToProdPair

/-- The explicit inverse map from `ℚ(i) × ℚ(i)` to `ℚ(i) ⊗[ℚ] ℚ(i)`. -/
noncomputable def ratSqrtNegOneProdToTensorSelf :
    ratSqrtNegOne × ratSqrtNegOne → ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne :=
  fun z ↦
    (((1 / 2 : ℚ) • (z.1 + z.2)) ⊗ₜ[ℚ] (1 : ratSqrtNegOne)) +
      (((-(1 / 2 : ℚ)) •
          ((z.1 - z.2) * AdjoinRoot.root ratSqrtNegOnePolynomial)) ⊗ₜ[ℚ]
        AdjoinRoot.root ratSqrtNegOnePolynomial)

/-- The tensor product `ℚ(i) ⊗[ℚ] ℚ(i)` splits as `ℚ(i) × ℚ(i)`. -/
noncomputable def ratSqrtNegOneTensorSelfEquivProd :
    ratSqrtNegOne ⊗[ℚ] ratSqrtNegOne ≃+* (ratSqrtNegOne × ratSqrtNegOne) where
  toFun := ratSqrtNegOneTensorSelfToProd
  invFun := ratSqrtNegOneProdToTensorSelf
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry

/-- The spectrum of `ℚ(i) ⊗[ℚ] ℚ(i)` is isomorphic to the spectrum of
`ℚ(i) × ℚ(i)`. -/
noncomputable def ratSqrtNegOneTensorSelfSpecIsoSpecProd :
    ratSqrtNegOneTensorSelfSpec ≅ Spec (CommRingCat.of (ratSqrtNegOne × ratSqrtNegOne)) where
  hom := Spec.map (ofHom ratSqrtNegOneTensorSelfEquivProd.symm.toRingHom)
  inv := Spec.map (ofHom ratSqrtNegOneTensorSelfEquivProd.toRingHom)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The self-fibre product of `Spec(ℚ(i))` over `Spec(ℚ)` is isomorphic to the coproduct of
two copies of `Spec(ℚ(i))`. -/
noncomputable def ratSqrtNegOneSelfFiberProductIsoCoprod :
    ratSqrtNegOneSelfFiberProduct ≅ ratSqrtNegOneSpec ⨿ ratSqrtNegOneSpec :=
  pullbackSpecIso ℚ ratSqrtNegOne ratSqrtNegOne ≪≫
    ratSqrtNegOneTensorSelfSpecIsoSpecProd ≪≫
      (asIso (coprodSpec ratSqrtNegOne ratSqrtNegOne)).symm

/-- The self-fibre product of `Spec(ℚ(i))` over `Spec(ℚ)` is reducible. -/
theorem ratSqrtNegOneSelfFiberProductReducible :
    ¬ IrreducibleSpace ratSqrtNegOneSelfFiberProduct := sorry

/-- The self-fibre product of the `ℚ`-variety `Spec(ℚ(i))` with itself over `Spec(ℚ)` is not
a variety. -/
theorem ratSqrtNegOneSelfFiberProductOverRatNotVariety :
    ¬ Variety ratSqrtNegOneSelfFiberProductOverRat := sorry

end AlgebraicGeometry
