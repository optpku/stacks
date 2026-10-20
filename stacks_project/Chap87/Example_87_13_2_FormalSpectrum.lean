module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.PresheafColimit
import StacksCheckRecall

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

export PresheafFormalSpectrum
  (spf IsDirectedAffineYonedaColimit specResidue stage_maximal_left)

/- Example 87.13.2: The presheaf formal spectrum is the weak-ideal Yoneda colimit. -/
@[stacks 0CB8] #check (AlgebraicGeometry.AffineFormalAlgebraicSpace.PresheafFormalSpectrum.spf :
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S),
    (Over S)ᵒᵖ ⥤ Type u)

end AlgebraicGeometry.AffineFormalAlgebraicSpace
