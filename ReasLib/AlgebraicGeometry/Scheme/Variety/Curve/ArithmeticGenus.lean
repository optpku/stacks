/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

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
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- The genus does not depend on the proofs of the dimension and global-functions hypotheses. -/
theorem genus_proof_irrel
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension h_dimension' : topologicalKrullDim X.left = 1)
    (hΓ hΓ' : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    genus X h_dimension hΓ = genus X h_dimension' hΓ' := sorry

end AlgebraicGeometry.SchemeOverField
