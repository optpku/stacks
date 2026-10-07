module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor

@[expose] public section

/-!
# Computation for cochain-to-homotopy comparisons

The comparison between termwise mapping before and after passage to a bounded homotopy
category is determined, after forgetting boundedness, by Mathlib's ambient factorization
isomorphism.
-/

open CategoryTheory
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

namespace Plus

/-- The underlying forward component of the bounded-below cochain-to-homotopy comparison
is the inverse ambient factorization component. -/
@[simp]
theorem quotientIso_hom_app_hom (F : C ⥤ D) [F.Additive]
    (K : CochainComplex.Plus C) :
    ((quotientIso F).hom.app K).hom =
      (F.mapHomotopyCategoryFactors (up ℤ)).inv.app K.obj := sorry

/-- The underlying inverse component of the bounded-below cochain-to-homotopy comparison
is the forward ambient factorization component. -/
@[simp]
theorem quotientIso_inv_app_hom (F : C ⥤ D) [F.Additive]
    (K : CochainComplex.Plus C) :
    ((quotientIso F).inv.app K).hom =
      (F.mapHomotopyCategoryFactors (up ℤ)).hom.app K.obj := sorry

end Plus

namespace Minus

/-- The underlying forward component of the bounded-above cochain-to-homotopy comparison
is the inverse ambient factorization component. -/
@[simp]
theorem quotientIso_hom_app_hom (F : C ⥤ D) [F.Additive]
    (K : CochainComplex.Minus C) :
    ((quotientIso F).hom.app K).hom =
      (F.mapHomotopyCategoryFactors (up ℤ)).inv.app K.obj := sorry

/-- The underlying inverse component of the bounded-above cochain-to-homotopy comparison
is the forward ambient factorization component. -/
@[simp]
theorem quotientIso_inv_app_hom (F : C ⥤ D) [F.Additive]
    (K : CochainComplex.Minus C) :
    ((quotientIso F).inv.app K).hom =
      (F.mapHomotopyCategoryFactors (up ℤ)).hom.app K.obj := sorry

end Minus

namespace Bounded

/-- The underlying forward component of the bounded cochain-to-homotopy comparison is the
inverse ambient factorization component. -/
@[simp]
theorem quotientIso_hom_app_hom (F : C ⥤ D) [F.Additive]
    (K : CochainComplex.Bounded C) :
    ((quotientIso F).hom.app K).hom =
      (F.mapHomotopyCategoryFactors (up ℤ)).inv.app K.obj := sorry

/-- The underlying inverse component of the bounded cochain-to-homotopy comparison is the
forward ambient factorization component. -/
@[simp]
theorem quotientIso_inv_app_hom (F : C ⥤ D) [F.Additive]
    (K : CochainComplex.Bounded C) :
    ((quotientIso F).inv.app K).hom =
      (F.mapHomotopyCategoryFactors (up ℤ)).hom.app K.obj := sorry

end Bounded

end CategoryTheory.Functor.Homotopy
