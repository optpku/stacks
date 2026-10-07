module

public import Mathlib.CategoryTheory.Category.Factorisation

@[expose] public section

/-!
# Composition of morphism factorisations

This file adds the two functorial operations that preserve the midpoint of a
`CategoryTheory.Factorisation`: precomposition at the source and postcomposition at the target.
-/

universe v u

namespace CategoryTheory.Factorisation

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C} {f : X ⟶ Y}

/-- The factorisation equation after precomposing the source map. -/
theorem precomp_condition (F : Factorisation f) (e : W ⟶ X) :
    (e ≫ F.ι) ≫ F.π = e ≫ f := sorry

/-- Precompose a factorisation while retaining its midpoint. -/
def precomp (F : Factorisation f) (e : W ⟶ X) : Factorisation (e ≫ f) where
  mid := F.mid
  ι := e ≫ F.ι
  π := F.π
  ι_π := precomp_condition F e

/-- The factorisation equation after postcomposing the target map. -/
theorem postcomp_condition (F : Factorisation f) (e : Y ⟶ Z) :
    F.ι ≫ (F.π ≫ e) = f ≫ e := sorry

/-- Postcompose a factorisation while retaining its midpoint. -/
def postcomp (F : Factorisation f) (e : Y ⟶ Z) : Factorisation (f ≫ e) where
  mid := F.mid
  ι := F.ι
  π := F.π ≫ e
  ι_π := postcomp_condition F e

end CategoryTheory.Factorisation
