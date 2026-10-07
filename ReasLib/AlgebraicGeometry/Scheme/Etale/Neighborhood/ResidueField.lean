module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/-- The residue field at the selected point of an étale neighbourhood carries
the canonical algebra structure over the residue field at the base point. -/
noncomputable instance residueFieldAlgebra {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) :
    Algebra (S.residueField s) (U.toEtale.left.residueField U.point) :=
  Eq.ndrec (motive := fun t : S ↦
      Algebra (S.residueField t) (U.toEtale.left.residueField U.point))
    (Scheme.Hom.residueFieldAlgebra U.toEtale.hom U.point) U.map_point

end AlgebraicGeometry.Scheme.EtaleNeighborhood
