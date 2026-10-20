module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.DualNumber

/-!
# Dual-number schemes and their residue projection

Typed checks preserve the dual-number scheme API for existing chapter imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (k : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specDualNumber openImmersion k :
    Over S)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specDualNumber_spec openImmersion k :
    (specDualNumber openImmersion k).left =
        Spec (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ∧
      (specDualNumber openImmersion k).hom =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (ArtinianLocalAlgCat.dualNumber Λ k).carrier)) ≫
          openImmersion)

variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specDualNumberToResidue_over openImmersion k kToS h_factor :
    Spec.map (CommRingCat.ofHom
          (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom) ≫
        kToS =
      (specDualNumber openImmersion k).hom)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specDualNumberToResidue openImmersion k kToS h_factor :
    specDualNumber openImmersion k ⟶ Over.mk kToS)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specDualNumberToResidue_spec openImmersion k kToS h_factor :
    (specDualNumberToResidue openImmersion k kToS h_factor).left =
      Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specDualNumberToResidue_comp openImmersion k kToS h_factor :
    specOver_toResidue openImmersion kToS h_factor (ArtinianLocalAlgCat.dualNumber Λ k) ≫
        specDualNumberToResidue openImmersion k kToS h_factor =
      𝟙 (Over.mk kToS))

end AlgebraicGeometry.GroupoidsOver.Predeformation
