module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Derived
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Scalar.Derived

/-!
# Derived Coextension along Quasi-isomorphisms of Cochain DG Algebras

Derived coextension from the base ring is compatible with derived extension of scalars along
a quasi-isomorphism of cochain differential graded algebras.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedBimodule

universe u

namespace CochainDGAlgebra.Hom.Derived

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, u} R}

/-- Derived coextension from the base ring to the target of a quasi-isomorphism is naturally
isomorphic to derived coextension to its source followed by derived extension of scalars. -/
noncomputable def coextensionFromBaseIsoExtension
    (f : A ⟶ B) (hf : CochainDGAlgebra.quasiIso f) :
    InternalHom.derivedFunctor
        (ChangeOfRings.restriction (CochainDGAlgebra.Hom.fromBase B)) ≅
      InternalHom.derivedFunctor
          (ChangeOfRings.restriction (CochainDGAlgebra.Hom.fromBase A)) ⋙
        extension f :=
  let directAdjunction :=
    TensorHom.derivedAdjunction
      (ChangeOfRings.restriction (CochainDGAlgebra.Hom.fromBase B))
  let compositeAdjunction :=
    (equivalence f hf).symm.toAdjunction.comp
      (TensorHom.derivedAdjunction
        (ChangeOfRings.restriction (CochainDGAlgebra.Hom.fromBase A)))
  let leftIso :=
    (restrictionIsoTensor (CochainDGAlgebra.Hom.fromBase B)).symm ≪≫
      (restrictionCompFromBaseIso f).symm ≪≫
      Functor.isoWhiskerLeft
        (restriction f)
        (restrictionIsoTensor (CochainDGAlgebra.Hom.fromBase A))
  (directAdjunction.ofNatIsoLeft leftIso).rightAdjointUniq compositeAdjunction

end CochainDGAlgebra.Hom.Derived
