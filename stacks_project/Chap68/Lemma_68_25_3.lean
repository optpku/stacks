module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Catenary.FiniteType
import StacksCheckRecall

/-!
# Catenary decent algebraic spaces of finite type

A decent algebraic space locally of finite type over a locally Noetherian
universally catenary scheme is catenary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.25.3: If `S` is a locally Noetherian universally catenary scheme
and `X` is a decent algebraic space over `S` whose structure morphism `X ⟶ S`
is locally of finite type, then `X` is catenary. -/
@[stacks 0ED6]
#check (AlgebraicGeometry.AlgebraicSpace.instIsCatenary_of_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [AlgebraicGeometry.UniversallyCatenary S]
    [LocallyOfFiniteType (SchemeRealization.toBase X)] [IsDecent X], IsCatenary X)

end AlgebraicGeometry.AlgebraicSpace
