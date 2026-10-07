module

public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap98.«98_3_0_2_SpecOver»

/-!
# Spec(k[ε]) as an object of `Over S`

The dual numbers `k[ε]` determine `Spec(k[ε]) ⟶ S` through a chosen affine open
`Spec(Λ) ⊂ S`, together with the structure map `Spec(k[ε]) ⟶ Spec(k)` over `S`.
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

/-- The object `Spec(k[ε]) ⟶ S` of `Over S` obtained from `ArtinianLocalAlgCat.dualNumber`. -/
def specDualNumber : Over S :=
  specOver openImmersion (ArtinianLocalAlgCat.dualNumber Λ k)

/-- `specDualNumber` is the morphism `Spec(k[ε]) ⟶ S` through the chosen affine open. -/
theorem specDualNumber_spec :
    (specDualNumber openImmersion k).left =
        Spec (CommRingCat.of (ArtinianLocalAlgCat.dualNumber Λ k).carrier) ∧
      (specDualNumber openImmersion k).hom =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (ArtinianLocalAlgCat.dualNumber Λ k).carrier)) ≫
          openImmersion :=
  sorry

variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]

/-- Compatibility of `Spec` of `residueToDualNumber` with the structure morphisms
`Spec(k[ε]) ⟶ S` and `Spec(k) ⟶ S`. -/
theorem specDualNumberToResidue_over
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    Spec.map (CommRingCat.ofHom
          (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom) ≫
        kToS =
      (specDualNumber openImmersion k).hom :=
  sorry

/-- The morphism `Spec(k[ε]) ⟶ Spec(k)` over `S`, induced by `residueToDualNumber`. -/
def specDualNumberToResidue
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    specDualNumber openImmersion k ⟶ Over.mk kToS :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom))
    (specDualNumberToResidue_over openImmersion k kToS h_factor)

/-- `specDualNumberToResidue` is `Spec` of `residueToDualNumber` as a morphism
`specDualNumber ⟶ Over.mk kToS`. -/
theorem specDualNumberToResidue_spec
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    (specDualNumberToResidue openImmersion k kToS h_factor).left =
      Spec.map (CommRingCat.ofHom
        (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom) :=
  sorry

/-- The residue projection `Spec(k) ⟶ Spec(k[ε])` followed by `specDualNumberToResidue`
is the identity on `Over.mk kToS`. -/
theorem specDualNumberToResidue_comp
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS) :
    specOver_toResidue openImmersion kToS h_factor (ArtinianLocalAlgCat.dualNumber Λ k) ≫
        specDualNumberToResidue openImmersion k kToS h_factor =
      𝟙 (Over.mk kToS) :=
  sorry


end AlgebraicGeometry.GroupoidsOver.Predeformation
