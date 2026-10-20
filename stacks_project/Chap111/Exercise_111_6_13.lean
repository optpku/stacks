module

import StacksCheckRecall
import ReasLib.Topology.Sober.GenericPoint

universe u

/- Exercise 111.6.13: in a T0 space `X`, every irreducible closed subset has at most one
generic point. -/
@[stacks 02D6]
#check (IsIrreducible.subsingleton_isGenericPoint :
  ∀ {X : Type u} [TopologicalSpace X] [T0Space X] {Z : Set X},
    IsIrreducible Z → IsClosed Z → Set.Subsingleton {x : X | IsGenericPoint x Z})

/- Companion: a set admitting a generic point is closed. -/
#check (IsGenericPoint.isClosed :
  ∀ {X : Type u} [TopologicalSpace X] {x : X} {Z : Set X},
    IsGenericPoint x Z → IsClosed Z)

/- Companion: a set admitting a generic point is irreducible. -/
#check (IsGenericPoint.isIrreducible :
  ∀ {X : Type u} [TopologicalSpace X] {x : X} {Z : Set X},
    IsGenericPoint x Z → IsIrreducible Z)
