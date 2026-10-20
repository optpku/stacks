module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.ResiduePredeformation

/-! # Formal objects in the residue-point predeformation category

Compatibility checks for the canonical residue-point conversion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.residueToS :
  ∀ (ξ : FormalObject X), Spec (CommRingCat.of (ResidueField ξ.base.carrier)) ⟶ S)

variable (ξ : FormalObject X)
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [Algebra Λ ξ.base.carrier] [Module.Finite Λ (ResidueField ξ.base.carrier)]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (h_toS : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
  openImmersion = ξ.base.toS)

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.toPredeformation ξ openImmersion h_toS :
  _root_.FormalObject (predeformationProjection ξ openImmersion h_toS))

section

variable [LocallyOfFiniteType (Predeformation.adicResidueToS ξ.base.toS)]

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.predeformationProjection
    ξ openImmersion h_toS :
  ULiftHom.{u + 1}
    (Predeformation.Obj openImmersion (Predeformation.adicResidueToS ξ.base.toS)
      (Predeformation.adicResidueFactor ξ.base.toS openImmersion h_toS)
      X (Predeformation.adicResidueFiber ξ.base.toS ξ.objects ξ.over_obj)) ⥤
    ArtinianLocalAlgCat Λ (ResidueField ξ.base.carrier))

end

end AlgebraicGeometry.GroupoidsOver.FormalObject
