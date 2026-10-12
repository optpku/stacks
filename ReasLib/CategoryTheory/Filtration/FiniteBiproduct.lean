/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Binary Biproducts of Finite Filtered Objects

This leaf records the closure facts that let Mathlib lift binary products from filtered objects to
the full subcategory of finite filtrations. The resulting biproducts are canonical full-subcategory
constructions, rather than a second hand-built additive presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

namespace IsFinite

/-- Finite filtrations are invariant under isomorphism of filtered objects. -/
@[stacks 05S1 "finite filtered biproducts"]
instance closedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFinite : ObjectProperty (FilteredObject C)) := sorry

/-- Finite filtrations are closed under binary products of filtered objects. -/
@[stacks 05S1 "finite filtered biproducts"]
instance closedUnderBinaryProducts
    [Preadditive C] [HasBinaryBiproducts C] :
    ObjectProperty.IsClosedUnderBinaryProducts
      (IsFinite : ObjectProperty (FilteredObject C)) := sorry

end IsFinite

namespace Finite

/-- Finite filtered objects inherit binary products from filtered objects. -/
@[stacks 05S1 "finite filtered biproducts"]
noncomputable instance hasBinaryProducts
    [Preadditive C] [HasBinaryBiproducts C] :
    HasBinaryProducts (FilteredObject.Finite.category C) :=
  inferInstance

/-- Finite filtered objects inherit binary biproducts from their canonical preadditive and
binary-product structures. -/
@[stacks 05S1 "finite filtered biproducts"]
noncomputable instance hasBinaryBiproducts
    [Preadditive C] [HasBinaryBiproducts C] :
    HasBinaryBiproducts (FilteredObject.Finite.category C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end Finite

end CategoryTheory.FilteredObject
