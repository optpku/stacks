module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints

/-!
# Irreducible components of algebraic spaces

An integral closed subspace is an irreducible component when its support is a
maximal irreducible subset. In a decent algebraic space these components
correspond to their unique generic points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- An integral closed subspace `Z ⊂ Y` whose point-set is an irreducible component
of `|Y|`. -/
def IsIrreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (Z : ClosedSubspace Y.X) : Prop :=
  IsIntegral Z.X ∧ Z.pointsSet ∈ irreducibleComponents (Points Y.X)

/-- Unpacking of `IsIrreducibleComponent`: integrality of `Z` together with `|Z|`
an irreducible component of `|Y|`. -/
theorem isIrreducibleComponent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (Z : ClosedSubspace Y.X) :
    IsIrreducibleComponent Y Z ↔
      IsIntegral Z.X ∧ Z.pointsSet ∈ irreducibleComponents (Points Y.X) :=
  Iff.rfl

/-- The canonical integral closed subspace of `Y` on a generic point of `|Y|`, given
by the reduced induced structure on the closure of that point. -/
noncomputable def irreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    ClosedSubspace Y.X :=
  ofIrreducibleClosed (irreducibleSetEquivPoints.toEquiv.symm η.1)

/-- The canonical closed subspace on a generic point of `|Y|` is an irreducible
component of `Y`. -/
theorem irreducibleComponent_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    IsIntegral (irreducibleComponent Y η).X ∧
      IsIrreducibleComponent Y (irreducibleComponent Y η) :=
  sorry

/-- The point-set of the canonical irreducible component on `η` is the closure of
`{η}`. -/
theorem pointsSet_irreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    (irreducibleComponent Y η).pointsSet = closure {η.1} :=
  sorry

/-- The generic point of an integral closed subspace `Z ⊂ Y`, as a point of `|Y|`. -/
noncomputable def genericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] : Points Y.X :=
  irreducibleSetEquivPoints.toEquiv Z.irreducibleClosed

/-- `genericPoint Z` is a generic point of the closed subset `|Z| ⊂ |Y|`. -/
theorem isGenericPoint_genericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] : IsGenericPoint (genericPoint Z) Z.pointsSet :=
  sorry

/-- The generic point of an irreducible component of `Y` lies in `genericPoints Y.X`. -/
theorem mem_genericPoints_genericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] (hZ : IsIrreducibleComponent Y Z) :
    genericPoint Z ∈ genericPoints Y.X :=
  sorry

/-- An integral closed subspace of `Y` with the same point-set as the canonical
irreducible component on `η` admits a unique morphism over `Y` to that component. -/
theorem existsUnique_hom_irreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X)
    (Z' : ClosedSubspace Y.X) [IsIntegral Z'.X]
    (h : Z'.pointsSet = (irreducibleComponent Y η).pointsSet) :
    ∃! g : Z'.X ⟶ (irreducibleComponent Y η).X,
      g ≫ (irreducibleComponent Y η).ι = Z'.ι :=
  sorry

end ClosedSubspace

/-- Every irreducible component of a decent algebraic space has a unique generic
point, whose singleton closure is the component. -/
theorem irreducibleComponents_equiv_genericPoints {S : Scheme.{u}}
    (Y : AlgebraicSpace S) [IsDecent Y]
    (T : irreducibleComponents (Points Y)) :
    ∃! ξ : Points Y,
      ξ ∈ genericPoints Y ∧
        closure ({ξ} : Set (Points Y)) = (T : Set (Points Y)) :=
  sorry

/-- Every irreducible component of a decent algebraic space has an integral closed
presentation, unique by a unique morphism over the ambient space. -/
theorem existsUnique_irreducibleComponent {S : Scheme.{u}}
    (Y : AlgebraicSpace S) [IsDecent Y]
    (T : irreducibleComponents (Points Y)) :
    ∃ Z : ClosedSubspace Y,
      IsIntegral Z.X ∧
        Z.pointsSet = (T : Set (Points Y)) ∧
          ∀ (Z' : ClosedSubspace Y),
            IsIntegral Z'.X →
              Z'.pointsSet = (T : Set (Points Y)) →
                ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
