module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences in the homotopy category

Bicategorical equivalences become ordinary isomorphisms after homwise `π₀` truncation.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory.HomotopyCategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace isoOfEquivalence

/-- The forward and inverse `1`-morphisms of a bicategorical equivalence become inverse after
passing to the homotopy category. -/
theorem hom_inv_id {X Y : B} (e : Bicategory.Equivalence X Y) :
    mkHom e.hom ≫ mkHom e.inv = 𝟙 (HomotopyCategory.mk X) := sorry

/-- The inverse and forward `1`-morphisms of a bicategorical equivalence become inverse after
passing to the homotopy category. -/
theorem inv_hom_id {X Y : B} (e : Bicategory.Equivalence X Y) :
    mkHom e.inv ≫ mkHom e.hom = 𝟙 (HomotopyCategory.mk Y) := sorry

end isoOfEquivalence

/-- A bicategorical equivalence induces an isomorphism in the homotopy `1`-category. -/
@[stacks 04SC "equivalences induce homotopy-category isomorphisms"]
def isoOfEquivalence {X Y : B} (e : Bicategory.Equivalence X Y) :
    HomotopyCategory.mk X ≅ HomotopyCategory.mk Y where
  hom := mkHom e.hom
  inv := mkHom e.inv
  hom_inv_id := isoOfEquivalence.hom_inv_id e
  inv_hom_id := isoOfEquivalence.inv_hom_id e

namespace isoOfEquivalence

/-- The forward map of the induced isomorphism is represented by the forward equivalence
morphism. -/
@[simp]
theorem hom {X Y : B} (e : Bicategory.Equivalence X Y) :
    (isoOfEquivalence e).hom = mkHom e.hom := sorry

/-- The inverse map of the induced isomorphism is represented by the inverse equivalence
morphism. -/
@[simp]
theorem inv {X Y : B} (e : Bicategory.Equivalence X Y) :
    (isoOfEquivalence e).inv = mkHom e.inv := sorry

end isoOfEquivalence

end CategoryTheory.Bicategory.HomotopyCategory
