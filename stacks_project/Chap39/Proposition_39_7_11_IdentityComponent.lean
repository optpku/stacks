module

public import ReasLib.AlgebraicGeometry.GroupScheme.IdentityComponent

universe u

/- Compatibility bridge for the canonical identity-component closed subgroup scheme. -/
#check (AlgebraicGeometry.GroupScheme.identityComponent :
  ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
    [CategoryTheory.GrpObj G], AlgebraicGeometry.Scheme.ClosedSubgroup G)
