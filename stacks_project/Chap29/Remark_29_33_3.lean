/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.ExternalTensor
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/-
Remark 29.33.3

For morphisms `X ⟶ S` and `Y ⟶ S`, external tensor product defines a functor from the
product of the additive categories of quasicoherent modules and finite-order relative
differential operators to the corresponding category on `X ×_S Y`; this functor is bilinear
on morphisms.
-/
@[stacks 0G46] #check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_externalTensorProductFunctor :
    ∀ {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S),
      ∃! T : AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat a ×
          AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat b ⥤
        AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat
          (Limits.pullback.fst a b ≫ a),
        AlgebraicGeometry.Scheme.Hom.IsExternalTensorProductFunctor a b T)

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat.instCategory :
    ∀ {X S : Scheme.{u}} (a : X ⟶ S),
      Category (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat a))

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat.instPreadditive :
    ∀ {X S : Scheme.{u}} (a : X ⟶ S),
      Preadditive (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat a))

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat.instHasFiniteBiproducts :
    ∀ {X S : Scheme.{u}} (a : X ⟶ S),
      HasFiniteBiproducts
        (AlgebraicGeometry.Scheme.Hom.FiniteOrderDifferentialOperatorCat a))

#check
  (AlgebraicGeometry.Scheme.Modules.externalTensorProduct :
    ∀ {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      (F : X.Modules) (G : Y.Modules), (Limits.pullback a b).Modules)

section Affine

variable {R M M' N N' : Type u}
variable [CommRing R]
variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
variable [Module R M] [Module R M'] [Module R N] [Module R N']

#check
  (TensorProduct.map :
    (M →ₗ[R] M') → (N →ₗ[R] N') →
      TensorProduct R M N →ₗ[R] TensorProduct R M' N')

#check
  (TensorProduct.map_tmul :
    ∀ (D : M →ₗ[R] M') (E : N →ₗ[R] N') (m : M) (n : N),
      TensorProduct.map D E (m ⊗ₜ[R] n) = D m ⊗ₜ[R] E n)

end Affine
