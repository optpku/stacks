/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of Property-Indexed Grothendieck Groups

An exact functor that carries one object property into another induces a map on the corresponding
Grothendieck groups.  This is the functorial counterpart to the inclusion map in
`ObjectProperty.GrothendieckGroup`.
-/

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.ObjectProperty.GrothendieckGroup

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- The object map of an exact functor kills the source property-indexed Grothendieck relations.
-/
theorem relations_le_ker_mapExact (F : A ⥤ₑ B) {P : ObjectProperty A} {Q : ObjectProperty B}
    (hF : ∀ X, P X → Q (F.obj.obj X)) :
    relations P ≤
      (FreeAbelianGroup.lift fun X : P.FullSubcategory ↦
        of Q ⟨F.obj.obj X.obj, hF X.obj X.property⟩).ker := sorry

/-- The homomorphism on property-indexed Grothendieck groups induced by an exact functor. -/
@[stacks 00JH "property-indexed Grothendieck exact-functor map"]
def mapExact (F : A ⥤ₑ B) {P : ObjectProperty A} {Q : ObjectProperty B}
    (hF : ∀ X, P X → Q (F.obj.obj X)) :
    ObjectProperty.GrothendieckGroup P →+ ObjectProperty.GrothendieckGroup Q :=
  lift (fun X : P.FullSubcategory ↦ of Q ⟨F.obj.obj X.obj, hF X.obj X.property⟩)
    (relations_le_ker_mapExact F hF)

/-- The exact-functor map sends a property-indexed class to the class of its image. -/
@[simp]
theorem mapExact_of (F : A ⥤ₑ B) {P : ObjectProperty A} {Q : ObjectProperty B}
    (hF : ∀ X, P X → Q (F.obj.obj X)) (X : P.FullSubcategory) :
    mapExact F hF (of P X) = of Q ⟨F.obj.obj X.obj, hF X.obj X.property⟩ := sorry

end CategoryTheory.ObjectProperty.GrothendieckGroup
