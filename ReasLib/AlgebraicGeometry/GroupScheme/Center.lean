module

public import ReasLib.CategoryTheory.Monoidal.Grp.Center
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.GroupScheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- A closed subgroup scheme represents the center when its inclusion uniquely receives every
central generalized point. -/
def IsCenter (K : Scheme.ClosedSubgroup G) : Prop :=
  ∀ (T : Over S) (g : T ⟶ G),
    GrpObj.IsCentral g ↔ ∃! z : T ⟶ K.left.X, z ≫ K.inclusion = g

/-- A closed subgroup scheme is the center exactly when its inclusion uniquely factors every
central generalized point. -/
theorem isCenter_iff (K : Scheme.ClosedSubgroup G) :
    IsCenter G K ↔ ∀ (T : Over S) (g : T ⟶ G),
      GrpObj.IsCentral g ↔ ∃! z : T ⟶ K.left.X, z ≫ K.inclusion = g := sorry

/-- The center of a locally algebraic group scheme over a field is represented by a closed
subgroup scheme. -/
theorem exists_center {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G]
    [LocallyAlgebraic G] : ∃ K : Scheme.ClosedSubgroup G, IsCenter G K := sorry

end AlgebraicGeometry.GroupScheme
