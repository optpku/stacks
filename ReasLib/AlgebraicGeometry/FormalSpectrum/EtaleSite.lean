module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleCompletion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine

/-!
# The affine étale site of a formal spectrum

The opposite affine étale site of the reduction of a weakly admissible formal
spectrum is equivalent to its category of completed étale algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The opposite affine étale site of a reduction of a weakly admissible formal
spectrum is equivalent to the category of completed étale algebras, whose
morphisms are all continuous algebra homomorphisms. -/
theorem spfAffineEtaleOppEquiv {S : Scheme.{u}} {B : Type u} [CommRing B]
    [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (R : ReductionData (spf B hB).obj) :
    Nonempty ((AlgebraicSpace.affineEtaleSite R.space)ᵒᵖ ≌ CommAlgCat.EtaleCompletion B) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
