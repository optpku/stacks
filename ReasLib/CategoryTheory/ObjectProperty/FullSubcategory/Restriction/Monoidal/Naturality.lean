/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Monoidal
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting monoidal natural transformations

The componentwise restriction of a monoidal natural transformation is again monoidal. This is
the 2-cell companion to the strong monoidal restriction functor.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}
variable [P.IsMonoidal] [Q.IsMonoidal]

/-- Restriction to full monoidal subcategories preserves monoidal natural transformations. -/
@[stacks 001D "restriction of a monoidal natural transformation"]
instance natTransIsMonoidal {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    NatTrans.IsMonoidal (natTrans hF hG α) := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
