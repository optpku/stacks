module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal

/-!
# Locally Noetherian closed subspaces

Closed immersions into locally Noetherian algebraic spaces have locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closed subscheme cut out by a quasi-coherent ideal in a Noetherian
algebraic space is Noetherian. -/
instance instIsNoetherian_subscheme {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    IsNoetherian (subscheme I) := sorry

/-- The source of a closed immersion into a locally Noetherian algebraic space is
locally Noetherian. -/
theorem IsLocallyNoetherian.of_isClosedImmersion {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] (i : Z ⟶ X)
    [hClosed : IsClosedImmersion i] : IsLocallyNoetherian Z :=
  LocallyOfFiniteType.isLocallyNoetherian i

/-- A closed subspace of a locally Noetherian algebraic space is locally
Noetherian. -/
def instIsLocallyNoetherian_of_isClosedImmersion {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (Z : ClosedSubspace X) :
    IsLocallyNoetherian Z.X :=
  IsLocallyNoetherian.of_isClosedImmersion Z.ι (hClosed := Z.isClosedImmersion)


end AlgebraicGeometry.AlgebraicSpace
