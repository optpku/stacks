module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Field
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober

@[expose] public section
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The separably closed geometric generic point is the separable-closure
point of the actual generic residue field followed by its canonical map to X. -/
def geometricGenericPoint :
    Spec (.of (SeparableClosure (X.residueField (genericPoint X)))) ⟶ X :=
  separableClosurePoint (X.residueField (genericPoint X)) ≫ X.fromSpecResidueField (genericPoint X)

/-- The corresponding actual point of the small étale site of X. -/
def genericEtalePoint : (smallEtaleTopology X).Point :=
  pointSmallEtale (geometricGenericPoint X)

/-- The geometric generic point has the actual generic point as its image. -/
theorem geometricGenericPoint_image : geometricGenericPoint X default = genericPoint X :=
  Scheme.fromSpecResidueField_apply (genericPoint X) _

/-- The field comparison at the actual generic residue field identifies its
absolute Galois group with the fundamental group of the generic-point scheme. -/
def genericGaloisEquiv :
    Gal(SeparableClosure (X.residueField (genericPoint X))/X.residueField (genericPoint X)) ≃*
      fundamentalGroup (separableClosurePoint (X.residueField (genericPoint X))) :=
  fieldGaloisEquiv (X.residueField (genericPoint X))

/-- The generic residue-field identification is an isomorphism of topological groups. -/
theorem genericGaloisEquiv_isHomeomorph : IsHomeomorph (genericGaloisEquiv X) :=
  fieldGaloisMap_isHomeomorph (X.residueField (genericPoint X))

/-- The canonical map on fundamental groups induced by the residue-field
point morphism Spec kappa(eta) to X, at its specified separable-closure point. -/
def genericPointFundamentalMap :
    ContinuousMonoidHom
      (fundamentalGroup (separableClosurePoint (X.residueField (genericPoint X))))
      (fundamentalGroup (geometricGenericPoint X)) :=
  Hom.fundamentalGroupMap (X.fromSpecResidueField (genericPoint X))
    (separableClosurePoint (X.residueField (genericPoint X)))

/-- The generic Galois homomorphism is the actual field fiber action followed
by fundamental-group functoriality for the generic-point inclusion. -/
def genericGaloisMap :
    ContinuousMonoidHom
      Gal(SeparableClosure (X.residueField (genericPoint X))/X.residueField (genericPoint X))
      (fundamentalGroup (geometricGenericPoint X)) :=
  (genericPointFundamentalMap X).comp (fieldGaloisMap (X.residueField (genericPoint X)))

/-- The generic Galois homomorphism factors through its specified field
identification in the source display order. -/
theorem genericGaloisMap_eq_comp :
    (genericGaloisMap X).toMonoidHom =
      (genericPointFundamentalMap X).toMonoidHom.comp (genericGaloisEquiv X).toMonoidHom := rfl

end AlgebraicGeometry.Scheme
