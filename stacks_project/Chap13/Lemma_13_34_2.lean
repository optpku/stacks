module

import ReasLib.CategoryTheory.DerivedCategory.Limit.Products
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.34.2

Exact countable products are handled by the shape-general product and homology
comparison APIs in `ReasLib`.  In particular, termwise products work for arbitrary
representative complexes; K-injectivity is not part of this lemma.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜] [HasCountableProducts 𝒜]
  [CountableAB4Star 𝒜]
variable (X : ℕ → DerivedCategory 𝒜) (K : ℕ → CochainComplex 𝒜 ℤ)
  (eK : ∀ i, DerivedCategory.Q.obj (K i) ≅ X i) (p : ℤ)

/- Lemma 13.34.2 (Stacks 07KC) (1): an abelian category with exact countable
products has countable products in its derived category. -/
@[stacks 07KC] #check
  (DerivedCategory.Product.hasProductsOfShape_of_exact (C := 𝒜) (J := ℕ) :
    HasProductsOfShape ℕ (DerivedCategory 𝒜))

/- Lemma 13.34.2 (Stacks 07KC) (2): localization preserves exact termwise
products, and the resulting representative-model fan is a product cone. -/
@[stacks 07KC] #check
  DerivedCategory.Product.q_preservesProduct_of_exact K

/- The universal-property half of Lemma 13.34.2 (Stacks 07KC) (2), after
transporting the localized representative family to the prescribed derived family. -/
@[stacks 07KC] #check
  DerivedCategory.Product.modelFanIsLimit X K eK

/- Lemma 13.34.2 (Stacks 07KC) (3): the canonical `Pi.lift` comparison from
homology of a termwise product to the product of homology objects is invertible. -/
@[stacks 07KC] #check
  DerivedCategory.Product.homologyProductComparison_isIso_of_exact p K

/- The projection characterization of the canonical comparison in Lemma
13.34.2 (Stacks 07KC) (3). -/
@[stacks 07KC] #check
  DerivedCategory.Product.homologyProductComparison_π p K

end CategoryTheory
