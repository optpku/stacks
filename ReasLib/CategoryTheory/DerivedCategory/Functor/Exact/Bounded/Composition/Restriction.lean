/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparisons for restricted exact derived functors

The ambient composition comparison for exact derived functors restricts to
arbitrary source, intermediate, and target full subcategories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ExactFunctor.Derived.Restriction

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-- Restrict the ambient exact-derived composition comparison to arbitrary
source, intermediate, and target object properties. -/
@[stacks 015F "restriction of the exact-derived composition comparison"]
noncomputable def compFunctorIso
    {P : ObjectProperty (DerivedCategory A)}
    {Q : ObjectProperty (DerivedCategory B)}
    {R : ObjectProperty (DerivedCategory C)}
    (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (hF : P ≤ Q.inverseImage F.mapDerivedCategory)
    (hG : Q ≤ R.inverseImage G.mapDerivedCategory)
    (hFG : P ≤ R.inverseImage (F.comp G).mapDerivedCategory) :
    restrict (F.comp G).mapDerivedCategory hFG ≅
      restrict F.mapDerivedCategory hF ⋙ restrict G.mapDerivedCategory hG :=
  restrict.natIso hFG (restrict.mapsToComp hF hG)
      (ExactFunctor.MapDerivedCategory.compFunctorIso F G) ≪≫
    restrict.compIso F.mapDerivedCategory G.mapDerivedCategory hF hG

namespace compFunctorIso

/-- The forward component of the restricted exact-derived composition
comparison is the ambient composition comparison. -/
@[simp, stacks 015F "restricted exact-derived composition forward component"]
theorem hom_app_hom
    {P : ObjectProperty (DerivedCategory A)}
    {Q : ObjectProperty (DerivedCategory B)}
    {R : ObjectProperty (DerivedCategory C)}
    (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (hF : P ≤ Q.inverseImage F.mapDerivedCategory)
    (hG : Q ≤ R.inverseImage G.mapDerivedCategory)
    (hFG : P ≤ R.inverseImage (F.comp G).mapDerivedCategory)
    (X : P.FullSubcategory) :
    ((Restriction.compFunctorIso F G hF hG hFG).hom.app X).hom =
      (ExactFunctor.MapDerivedCategory.compObjIso F G X.obj).hom := sorry

/-- The inverse component of the restricted exact-derived composition
comparison is the inverse ambient composition comparison. -/
@[simp, stacks 015F "restricted exact-derived composition inverse component"]
theorem inv_app_hom
    {P : ObjectProperty (DerivedCategory A)}
    {Q : ObjectProperty (DerivedCategory B)}
    {R : ObjectProperty (DerivedCategory C)}
    (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (hF : P ≤ Q.inverseImage F.mapDerivedCategory)
    (hG : Q ≤ R.inverseImage G.mapDerivedCategory)
    (hFG : P ≤ R.inverseImage (F.comp G).mapDerivedCategory)
    (X : P.FullSubcategory) :
    ((Restriction.compFunctorIso F G hF hG hFG).inv.app X).hom =
      (ExactFunctor.MapDerivedCategory.compObjIso F G X.obj).inv := sorry

end compFunctorIso

end CategoryTheory.ExactFunctor.Derived.Restriction
