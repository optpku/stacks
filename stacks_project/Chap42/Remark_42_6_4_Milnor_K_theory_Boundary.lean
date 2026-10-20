module

public import ReasLib.AlgebraicGeometry.MilnorK.Coniveau

open AlgebraicGeometry
open MilnorK MilnorK.Coniveau
open scoped BigOperators TensorProduct

universe u v

/- Compatibility checks for the homogeneous Milnor groups, local residues, and
specialization geometry used by pointwise cycle constructions. -/
#check (MilnorK.degreeZeroMap_bijective :
  ∀ (k : Type u) [Field k],
    Function.Bijective (degreeZeroMap k))

#check (MilnorK.boundaryOneOnGroup :
  ∀ (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1),
    Group 2 F →+ Group 1 (IsLocalRing.ResidueField A))

#check (MilnorK.Coniveau.specializationResidueFieldMap :
  ∀ {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y),
    IsLocalRing.ResidueField (SpecializationLocalRing hxy.specializes) →+*
      X.residueField y)

