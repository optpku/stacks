module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.CategoryTheory.Functor.Derived.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition with an exact second functor

For bounded-below right-derived functors, the canonical comparison
`R(F ⋙ G) ⟶ RF ⋙ RG` is invertible when the second functor `G` is exact.  The instance in this
leaf makes that canonical fact available without rebuilding local comparison instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB wC vA vB vC uA uB uC

namespace CategoryTheory.Functor.RightDerived.Composition.BoundedBelow

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wC} C]

/-- If the second functor is exact, the bounded-below right-derived composition comparison is
an isomorphism. -/
@[stacks 015M "exact second functor"]
noncomputable instance comparisonIsIsoOfSecondExact
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [EnoughInjectives A] [EnoughInjectives B]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    IsIso (comparison F G) := sorry

end CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
