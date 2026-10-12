/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Limit.CountableCoproduct
public import ReasLib.CategoryTheory.DerivedCategory.Limit.CountableProduct
public import ReasLib.CategoryTheory.Limits.CoproductToProduct
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Coproducts and Products of Shifted Families

For a `ℤ`-indexed family `M`, this module names the family `M n[-n]` in a derived category and its
canonical coproduct-to-product comparison. Exact countable coproducts and products make that
comparison invertible; the Grothendieck case is a specialization of this neutral statement.
-/

open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.ShiftedFamily

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The derived family whose `n`-th object is `M n` placed in cohomological degree `n`. -/
@[stacks 07DA "shifted family"]
abbrev objects (M : ℤ → A) (n : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A n).obj (M n)

/-- The canonical map from the coproduct of `M n[-n]` to the product of the same family. -/
@[stacks 07DA "coproduct-to-product comparison"]
def comparison (M : ℤ → A)
    [HasCoproduct (objects M)] [HasProduct (objects M)] :
    (∐ objects M) ⟶ ∏ᶜ objects M :=
  coproductToProduct (objects M)

/-- The `n`-th product component of the shifted-family comparison is the canonical coproduct
projection. -/
@[reassoc (attr := simp)]
theorem comparison_π (M : ℤ → A)
    [HasCoproduct (objects M)] [HasProduct (objects M)] (n : ℤ) :
    comparison M ≫ Pi.π (objects M) n = Sigma.π (objects M) n := sorry

/-- The diagonal component of the shifted-family comparison is the identity. -/
@[reassoc (attr := simp)]
theorem ι_comparison_π (M : ℤ → A)
    [HasCoproduct (objects M)] [HasProduct (objects M)] (n : ℤ) :
    Sigma.ι (objects M) n ≫ comparison M ≫ Pi.π (objects M) n =
      𝟙 (objects M n) := sorry

/-- In an abelian category with exact countable coproducts and products, the canonical map
`⨁ M n[-n] ⟶ ∏ M n[-n]` is an isomorphism. This is the assumption-minimal form of
Remark 19.13.5. -/
@[stacks 07DA "countable AB4 and AB4-star form", instance]
theorem comparison_isIso
    [HasCountableCoproducts A] [CountableAB4 A]
    [HasCountableProducts A] [CountableAB4Star A]
    (M : ℤ → A) : IsIso (comparison M) := sorry

end CategoryTheory.DerivedCategory.ShiftedFamily
