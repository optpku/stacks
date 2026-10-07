module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded exact-derived homology comparisons

The homology comparisons on bounded-below, bounded-above, and bounded
derived categories are natural in morphisms of bundled exact functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B]

namespace Plus.homologyFunctorIso

/-- The forward bounded-below homology comparison is natural in morphisms
of bundled exact functors. -/
@[reassoc, stacks 015F "naturality of bounded-below exact-derived homology"]
theorem naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerRight (Plus.map α)
          (DerivedCategory.Plus.homologyFunctor B q) ≫
        (Plus.homologyFunctorIso G q).hom =
      (Plus.homologyFunctorIso F q).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Plus.homologyFunctor A q) α.hom := sorry

/-- The inverse bounded-below homology comparison is natural in morphisms
of bundled exact functors. -/
@[reassoc]
theorem inv_naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerLeft
          (DerivedCategory.Plus.homologyFunctor A q) α.hom ≫
        (Plus.homologyFunctorIso G q).inv =
      (Plus.homologyFunctorIso F q).inv ≫
        Functor.whiskerRight (Plus.map α)
          (DerivedCategory.Plus.homologyFunctor B q) := sorry

end Plus.homologyFunctorIso

namespace Minus.homologyFunctorIso

/-- The forward bounded-above homology comparison is natural in morphisms
of bundled exact functors. -/
@[reassoc, stacks 015F "naturality of bounded-above exact-derived homology"]
theorem naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerRight (Minus.map α)
          (DerivedCategory.Minus.homologyFunctor B q) ≫
        (Minus.homologyFunctorIso G q).hom =
      (Minus.homologyFunctorIso F q).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Minus.homologyFunctor A q) α.hom := sorry

/-- The inverse bounded-above homology comparison is natural in morphisms
of bundled exact functors. -/
@[reassoc]
theorem inv_naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerLeft
          (DerivedCategory.Minus.homologyFunctor A q) α.hom ≫
        (Minus.homologyFunctorIso G q).inv =
      (Minus.homologyFunctorIso F q).inv ≫
        Functor.whiskerRight (Minus.map α)
          (DerivedCategory.Minus.homologyFunctor B q) := sorry

end Minus.homologyFunctorIso

namespace Bounded.homologyFunctorIso

/-- The forward bounded homology comparison is natural in morphisms of
bundled exact functors. -/
@[reassoc, stacks 015F "naturality of bounded exact-derived homology"]
theorem naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerRight (Bounded.map α)
          (DerivedCategory.Bounded.homologyFunctor B q) ≫
        (Bounded.homologyFunctorIso G q).hom =
      (Bounded.homologyFunctorIso F q).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Bounded.homologyFunctor A q) α.hom := sorry

/-- The inverse bounded homology comparison is natural in morphisms of
bundled exact functors. -/
@[reassoc]
theorem inv_naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerLeft
          (DerivedCategory.Bounded.homologyFunctor A q) α.hom ≫
        (Bounded.homologyFunctorIso G q).inv =
      (Bounded.homologyFunctorIso F q).inv ≫
        Functor.whiskerRight (Bounded.map α)
          (DerivedCategory.Bounded.homologyFunctor B q) := sorry

end Bounded.homologyFunctorIso

end CategoryTheory.ExactFunctor.Derived
