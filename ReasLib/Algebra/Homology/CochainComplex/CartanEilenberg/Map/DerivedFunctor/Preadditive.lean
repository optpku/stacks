module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.DerivedFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.PagesFunctor.Preadditive

/-!
# Additive derived-page target functors

The right-derived target functors used by the initial-page comparisons are additive.  These
instances make the comparison layer compositional with the page functors without local instance
pins.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace First.Derived

/-- The termwise right-derived source-complex functor is additive. -/
@[stacks 015J "additivity of the first derived source-complex functor"]
noncomputable instance complex_additive (F : A ⥤ B) [F.Additive] (q : ℕ) :
    (complex F q).Additive := sorry

/-- The first derived page-two target functor is additive. -/
@[stacks 015J "additivity of the first derived page-two functor"]
noncomputable instance homology_additive (F : A ⥤ B) [F.Additive] (p : ℤ) (q : ℕ) :
    (homology F p q).Additive := sorry

end First.Derived

namespace Second.Derived

/-- The second derived page-two target functor is additive. -/
@[stacks 015J "additivity of the second derived page-two functor"]
noncomputable instance homology_additive (F : A ⥤ B) [F.Additive] (p : ℕ) (q : ℤ) :
    (homology F p q).Additive := sorry

end Second.Derived

end CochainComplex.CartanEilenbergResolution.Bundled
