/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
public import ReasLib.CategoryTheory.Preadditive.Injective.Closure
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Limits of Finite Filtered-Injective Objects

Finite filtered-injective objects contain a zero object and are closed under finite products.
Mathlib's object-property infrastructure therefore equips their full subcategory with the
canonical zero-object, finite-product, and finite-biproduct instances.
-/

@[expose] public section

open CategoryTheory Limits ObjectProperty

universe v u

noncomputable section

namespace CategoryTheory

namespace FilteredObject.Finite.FilteredInjective

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

namespace property

/-- Finite filtered-injective objects contain a zero object. -/
instance containsZero : (property C).ContainsZero := sorry

/-- Finite filtered-injective objects are closed under finite products. -/
instance closedUnderFiniteProducts :
    (property C).IsClosedUnderFiniteProducts := sorry

end property

namespace category

/-- The finite filtered-injective full subcategory inherits binary biproducts from its canonical
binary products and preadditive structure. -/
noncomputable instance hasBinaryBiproducts :
    HasBinaryBiproducts (category C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end category

#synth HasZeroObject (category C)
#synth HasBinaryProducts (category C)
#synth HasBinaryBiproducts (category C)

end FilteredObject.Finite.FilteredInjective

end CategoryTheory
