/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u
variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-!
# Definition 13.34.1

The presentation-independent owner is `HomotopyLimit.IsOf`. It quantifies an explicit product
cone rather than storing a `HasProduct` instance. `HomotopyLimit.Presentation` is the reusable
data surface when downstream code needs the product projections or the Milnor triangle itself.
The separate neutral `ProductCone.R1` API retains the Milnor-cokernel construction, with
`ProductCone.canonicalR1` preserving the selected-product computation model.
-/

#check @CategoryTheory.SequentialInverseSystem.family
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.R1
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.R1.map
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1.map
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1.explicit_eq
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.projection
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.difference
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.difference_comp_projection

@[stacks 08TC] #check @CategoryTheory.HomotopyLimit.IsOf

#check @CategoryTheory.HomotopyLimit.Presentation
#check @CategoryTheory.HomotopyLimit.Presentation.triangle
#check @CategoryTheory.HomotopyLimit.Presentation.stageProjection
#check @CategoryTheory.HomotopyLimit.Presentation.stageProjection_naturality
#check @CategoryTheory.HomotopyLimit.Presentation.isOf
#check @CategoryTheory.HomotopyLimit.IsOf.nonemptyPresentation_iff
#check @CategoryTheory.HomotopyLimit.IsOf.inverseSystem
#check @CategoryTheory.HomotopyLimit.IsOf.isClosedUnderIsomorphisms
#check @CategoryTheory.HomotopyLimit.IsOf.inverseSystemIsClosedUnderIsomorphisms
#check @CategoryTheory.ObjectProperty.prop_iff_of_iso
#check @CategoryTheory.ObjectProperty.prop_iff_of_isIso
#check @CategoryTheory.HomotopyLimit.Comparison
#check @CategoryTheory.HomotopyLimit.Comparison.comp_stageProjection
