/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.AffineProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open CategoryTheory.Limits.ProductsFromFiniteCofiltered

noncomputable section

universe u

variable {I : Type u} (S : Scheme.{u})
variable (T : I → Over S)
variable [∀ i, IsAffineHom (T i).hom]

/- Lemma 32.3.1: an indexed family of affine morphisms into `S` admits a
product in `Over S`. -/
@[stacks 0CNI] #check
  (AlgebraicGeometry.Scheme.Over.instHasProductOfIsAffineHom S T : HasProduct T)

/- The product is the limit of its finite subproducts. -/
#check
  (CategoryTheory.Limits.ProductsFromFiniteCofiltered.isLimitFiniteSubproductsConeOfHasProduct T :
    IsLimit (finiteSubproductsCone T))

/- Every projection from the product to a finite subproduct is affine. -/
#check
  (AlgebraicGeometry.Scheme.Over.isAffineHom_finiteSubproductsCone_π_app S T :
    ∀ s : (Finset (Discrete I))ᵒᵖ,
      IsAffineHom ((finiteSubproductsCone T).π.app s).left)
