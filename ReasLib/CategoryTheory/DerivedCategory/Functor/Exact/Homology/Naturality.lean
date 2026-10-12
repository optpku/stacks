/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of exact-derived homology comparisons

The canonical comparison between applying an exact functor before homology
and applying it after homology is natural in the exact functor.  These
squares are the 2-cell API for the homology comparison.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.homologyFunctorIso

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B]

/-- The forward exact-derived homology comparison is natural in morphisms
of bundled exact functors. -/
@[reassoc, stacks 015F "naturality of exact-derived homology comparison"]
theorem naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerRight (MapDerivedCategory.map α)
          (DerivedCategory.homologyFunctor B q) ≫
        (G.homologyFunctorIso q).hom =
      (F.homologyFunctorIso q).hom ≫
        Functor.whiskerLeft (DerivedCategory.homologyFunctor A q) α.hom := sorry

/-- The inverse exact-derived homology comparison is natural in morphisms
of bundled exact functors. -/
@[reassoc, stacks 015F "inverse naturality of exact-derived homology comparison"]
theorem inv_naturality {F G : A ⥤ₑ B} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerLeft (DerivedCategory.homologyFunctor A q) α.hom ≫
        (G.homologyFunctorIso q).inv =
      (F.homologyFunctorIso q).inv ≫
        Functor.whiskerRight (MapDerivedCategory.map α)
          (DerivedCategory.homologyFunctor B q) := sorry

end CategoryTheory.ExactFunctor.homologyFunctorIso
