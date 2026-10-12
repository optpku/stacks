/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Products and Coproducts in Homotopy Categories

Products and coproducts of homological complexes descend through the quotient by homotopy.
This is specific to discrete diagram shapes: it does not assert that a homotopy category has
general limits or colimits.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u w t

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type w} (c : ComplexShape ι) (J : Type t)

/-- Stacks 09JR: coproducts in a preadditive category induce coproducts in the homotopy
category of complexes. -/
@[stacks 09JR "coproducts in homotopy categories"]
instance hasCoproductsOfShape [HasCoproductsOfShape J C] :
    HasCoproductsOfShape J (HomotopyCategory C c) := sorry

/-- Stacks 09JR: a preadditive category with arbitrary coproducts has a homotopy category with
arbitrary coproducts. -/
@[stacks 09JR "arbitrary coproducts in homotopy categories"]
instance hasCoproducts [HasCoproducts.{t} C] :
    HasCoproducts.{t} (HomotopyCategory C c) := sorry

/-- Stacks 09JR: the quotient from complexes to their homotopy category preserves
coproducts. -/
@[stacks 09JR "homotopy quotient preserves coproducts"]
instance quotient_preservesCoproductsOfShape [HasCoproductsOfShape J C] :
    PreservesColimitsOfShape (Discrete J) (quotient C c) := sorry

/-- Stacks 09JR: products in a preadditive category induce products in the homotopy category
of complexes. -/
@[stacks 09JR "products in homotopy categories"]
instance hasProductsOfShape [HasProductsOfShape J C] :
    HasProductsOfShape J (HomotopyCategory C c) := sorry

/-- Stacks 09JR: a preadditive category with arbitrary products has a homotopy category with
arbitrary products. -/
@[stacks 09JR "arbitrary products in homotopy categories"]
instance hasProducts [HasProducts.{t} C] :
    HasProducts.{t} (HomotopyCategory C c) := sorry

/-- Stacks 09JR: the quotient from complexes to their homotopy category preserves products. -/
@[stacks 09JR "homotopy quotient preserves products"]
instance quotient_preservesProductsOfShape [HasProductsOfShape J C] :
    PreservesLimitsOfShape (Discrete J) (quotient C c) := sorry

end HomotopyCategory
