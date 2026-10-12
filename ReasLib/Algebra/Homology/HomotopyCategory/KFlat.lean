/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat objects in the homotopy category

@stack 06XZ
@stack 0FPB

This file owns the object property of K-flat cochain complexes in the homotopy category.
Closure properties and extra structures are supplied by separate leaves.
-/

@[expose] public section

open CategoryTheory ComplexShape

universe u v w

namespace CategoryTheory.HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

section Shape

variable {I : Type w} [AddMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]

/-- A homotopy-category object is K-flat when its representative homological complex is K-flat. -/
@[stacks 06XZ "homotopy-category form"]
abbrev IsKFlat (K : HomotopyCategory C c) : Prop :=
  HomologicalComplex.IsKFlat K.as

/-- K-flatness of a homotopy-category object is K-flatness of its representative complex. -/
theorem isKFlat_iff (K : HomotopyCategory C c) :
    K.IsKFlat ↔ HomologicalComplex.IsKFlat K.as := sorry

end Shape

/-- K-flat cochain complexes in the homotopy category, as an object property. -/
@[stacks 0FPB "K-flat homotopy objects"]
def kFlat (C : Type u) [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] :
    ObjectProperty (HomotopyCategory C (up ℤ)) :=
  fun K ↦ K.IsKFlat

/-- The full subcategory of K-flat cochain complexes in the homotopy category. -/
abbrev KFlat (C : Type u) [Category.{v} C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] :=
  (kFlat C).FullSubcategory

/-- Membership in `kFlat C` is K-flatness of the represented cochain complex. -/
theorem mem_kFlat (K : HomotopyCategory C (up ℤ)) :
    kFlat C K ↔ K.IsKFlat := sorry

namespace KFlat

/-- K-flat homotopy objects are closed under isomorphisms. -/
@[stacks 06XZ "isomorphism stability of K-flat homotopy objects"]
instance isClosedUnderIsomorphisms :
    (kFlat C).IsClosedUnderIsomorphisms := sorry

end KFlat



end CategoryTheory.HomotopyCategory
