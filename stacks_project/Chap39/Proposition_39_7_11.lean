module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.IdentityComponent

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

universe u

/- Proposition 39.7.11 (1): The canonical identity-component closed subgroup scheme. -/
@[stacks 0B7R] #check (AlgebraicGeometry.GroupScheme.identityComponent :
  ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G], Scheme.ClosedSubgroup G)

/- Proposition 39.7.11 (2): Its inclusion is a flat closed immersion. -/
@[stacks 0B7R] #check (AlgebraicGeometry.GroupScheme.instFlatIdentityComponent :
  ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G],
    Flat (AlgebraicGeometry.GroupScheme.identityComponent G).inclusion.left)

/- Proposition 39.7.11 (3): Its image is the connected component of the identity. -/
@[stacks 0B7R] #check (AlgebraicGeometry.GroupScheme.range_identityComponent :
  ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G],
    Set.range (AlgebraicGeometry.GroupScheme.identityComponent G).inclusion.left =
      connectedComponent (η[G].left (IsLocalRing.closedPoint k)))

/- Proposition 39.7.11 (4): It is geometrically irreducible over the base field. -/
@[stacks 0B7R] #check
  (AlgebraicGeometry.GroupScheme.instGeometricallyIrreducibleIdentityComponent :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G],
      GeometricallyIrreducible
        (AlgebraicGeometry.GroupScheme.identityComponent G).left.X.hom)

/- Proposition 39.7.11 (5): Its underlying space is quasi-compact. -/
@[stacks 0B7R] #check (AlgebraicGeometry.GroupScheme.instCompactSpaceIdentityComponent :
  ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G],
    CompactSpace (AlgebraicGeometry.GroupScheme.identityComponent G).left.X.left)
