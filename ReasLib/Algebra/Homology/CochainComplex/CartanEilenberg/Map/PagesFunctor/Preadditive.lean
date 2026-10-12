/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Pages.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.PagesFunctor

/-!
# Additive initial-page functors of Cartan--Eilenberg resolutions

The page-one complexes and page-two entries assembled on bundled resolutions inherit additivity
from the page-map API.  These instances are kept separate from the page definitions so clients
can import the computation layer without changing the neutral functor owner.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [CategoryWithHomology B]

namespace First

/-- The first page-one functor is additive in the resolution. -/
@[stacks 015J "additivity of the first page-one functor"]
noncomputable instance pageOne_additive (F : A ⥤ B) [F.Additive] (q : ℤ) :
    (pageOne F q).Additive := sorry

/-- The first page-two functor is additive in the resolution. -/
@[stacks 015J "additivity of the first page-two functor"]
noncomputable instance pageTwo_additive (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    (pageTwo F p q).Additive := sorry

end First

namespace Second

/-- The second page-one functor is additive in the resolution. -/
@[stacks 015J "additivity of the second page-one functor"]
noncomputable instance pageOne_additive (F : A ⥤ B) [F.Additive] (q : ℤ) :
    (pageOne F q).Additive := sorry

/-- The second page-two functor is additive in the resolution. -/
@[stacks 015J "additivity of the second page-two functor"]
noncomputable instance pageTwo_additive (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    (pageTwo F p q).Additive := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Bundled
