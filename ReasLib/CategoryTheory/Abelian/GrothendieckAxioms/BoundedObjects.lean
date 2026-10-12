/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.CategoryTheory.Abelian.SubobjectCardinal
public import ReasLib.CategoryTheory.ObjectProperty.Representatives
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Objects in Grothendieck Abelian Categories

The canonical separator of a Grothendieck abelian category specializes the general bounded
subobject-cardinality API to a reusable essential-smallness instance and a set of isomorphism
class representatives.
-/

open CategoryTheory

universe w v u

namespace CategoryTheory.ObjectProperty.SubobjectCardinal

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Objects with subobject cardinality at most `kappa` form an essentially small property in a
Grothendieck abelian category. -/
@[stacks 079E "bounded objects are essentially small"]
instance essentiallySmall_le (kappa : Cardinal.{max u v}) [Small.{w} kappa.out] :
    ObjectProperty.EssentiallySmall.{w}
      (ObjectProperty.subobjectCardinalLE (C := C) kappa) := sorry

end CategoryTheory.ObjectProperty.SubobjectCardinal
