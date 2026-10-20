module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The genus of a proper curve is the dimension of the first cohomology of its structure
sheaf. -/
noncomputable def genusOfCurve
    {k : Type u} [Field k] (X : SchemeOverField k) [AlgebraicGeometry.Curve X]
    [IsProper X.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1

/-- The genus of a proper curve is its degree-one structure-sheaf cohomology dimension. -/
theorem genusOfCurve_def
    {k : Type u} [Field k] (X : SchemeOverField k) [AlgebraicGeometry.Curve X]
    [IsProper X.hom] :
    genusOfCurve X = Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := rfl

/-- The genus of a proper one-dimensional scheme over a field whose global functions are
exactly that field is the dimension of the first cohomology of its structure sheaf. -/
noncomputable def genus
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (_ : topologicalKrullDim X.left = 1)
    (_ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1

/-- The genus is the degree-one cohomology dimension of the structure sheaf. -/
theorem genus_def
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    genus X h_dimension hΓ = Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := rfl

/-- The genus does not depend on the proofs of the dimension and global-functions hypotheses. -/
theorem genus_proof_irrel
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension h_dimension' : topologicalKrullDim X.left = 1)
    (hΓ hΓ' : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    genus X h_dimension hΓ = genus X h_dimension' hΓ' := rfl

end AlgebraicGeometry.SchemeOverField
