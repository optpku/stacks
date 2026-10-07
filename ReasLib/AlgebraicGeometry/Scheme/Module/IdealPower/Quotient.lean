module

public import ReasLib.Algebra.Module.IdealPower.ModuleCat
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Comparison
public import ReasLib.LinearAlgebra.Quotient.Representative

/-!
# Quotient Hom-to-sections comparison over an affine ideal complement

This is the quotient counterpart of the Hom comparison API.  It uses the
canonical ideal-power torsion quotients and keeps an explicit finite generating
family available for applications that already carry cover data.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry PrimeSpectrum
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The quotient class evaluated by a stage Hom map at the powered generator `fᵢ^n`. -/
noncomputable def idealPowerQuotientHomLocalClassUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerQuotientHom M n) (i : G.Index) :
    M ⧸ I.powerAnnihilatedSubmodule M n :=
  φ ⟨(G.generator i) ^ n, Ideal.pow_mem_pow (G.generator_mem i) n⟩

/-- The chosen numerator used by the quotient-Hom local section represents the prescribed quotient
class.  Downstream proofs should use this specification rather than unfold the choice. -/
noncomputable def idealPowerQuotientHomLocalRepresentativeUsing
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ)
    (φ : I.powerQuotientHom M n) (i : G.Index) : M :=
  Submodule.quotientRepresentative
    (I.powerAnnihilatedSubmodule M n)
    (idealPowerQuotientHomLocalClassUsing G M n φ i)

/-- The chosen local representative maps to the prescribed quotient class.  Downstream proofs
should use this specification rather than unfold the representative choice. -/
@[simp]
theorem idealPowerQuotientHomLocalRepresentativeUsing_mkQ (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerQuotientHom M n) (i : G.Index) :
    (I.powerAnnihilatedSubmodule M n).mkQ
        (idealPowerQuotientHomLocalRepresentativeUsing G M n φ i) =
      idealPowerQuotientHomLocalClassUsing G M n φ i := sorry

/-- The local section on the `i`-th basic open associated to a map
`I^n →ₗ[A] M / M_n`, using an explicit finite generating family of `I`. -/
noncomputable def idealPowerQuotientHomLocalSectionUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerQuotientHom M n) (i : G.Index) :
    ((tildePresheaf M).obj (Opposite.op (G.basicOpen i)) : Type u) :=
  tildeBasicOpenPowerSection M (G.generator i) n
    (idealPowerQuotientHomLocalRepresentativeUsing G M n φ i)

/-- Equality in an ideal-power annihilated quotient gives equal local sections on the
corresponding basic open. -/
theorem tildeBasicOpenPowerSection_eq_of_powerAnnihilatedQuotient_eq
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ)
    (i : G.Index) {x y : M}
    (hxy : (I.powerAnnihilatedSubmodule M n).mkQ x =
      (I.powerAnnihilatedSubmodule M n).mkQ y) :
    tildeBasicOpenPowerSection M (G.generator i) n x =
      tildeBasicOpenPowerSection M (G.generator i) n y := sorry

/-- The quotient local fractions associated to an ideal-power Hom map are compatible on the
chosen basic-open cover. -/
theorem idealPowerQuotientHomLocalSectionUsing_compatible (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerQuotientHom M n) :
    TopCat.Presheaf.IsCompatible
      (tildePresheaf M)
      G.basicOpen
      (idealPowerQuotientHomLocalSectionUsing G M n φ) := sorry

/-- The finite-cover stage data for the quotient ideal-power Hom comparison.  It records only
the quotient-valued local-fraction formula and its compatibility. -/
noncomputable def idealPowerQuotientHomStageUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) : IdealComplementStage G M where
  stage := I.powerQuotientHomModuleStage M
  transition := fun n ↦ I.powerQuotientHomModuleTransition M n
  localSection := fun n φ i ↦ idealPowerQuotientHomLocalSectionUsing G M n φ i
  compatible := fun n φ ↦ idealPowerQuotientHomLocalSectionUsing_compatible G M n φ

/-- The canonical glued sections of the quotient ideal-power Hom stage are linear and commute
with its transition maps. -/
theorem idealPowerQuotientHomStageUsing_isLinear (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) : (idealPowerQuotientHomStageUsing G M).IsLinear := sorry

/-- The section of `tilde M` on `Spec A ∖ V(I)` induced by one quotient Hom stage, using an
explicit finite generating family. -/
noncomputable def idealPowerQuotientHomSectionAtStageUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerQuotientHom M n) :
    idealComplementTildeSections I M :=
  (idealPowerQuotientHomStageUsing G M).gluedSection n φ

/-- Restricting a stagewise quotient Hom section to a chosen basic open gives its prescribed
local fraction. -/
theorem idealPowerQuotientHomSectionAtStageUsing_spec (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerQuotientHom M n) (i : G.Index) :
    (tildePresheaf M).map (homOfLE (G.basicOpen_le_idealComplementOpens i)).op
        (idealPowerQuotientHomSectionAtStageUsing G M n φ) =
      idealPowerQuotientHomLocalSectionUsing G M n φ i := sorry

/-- The stagewise quotient comparison map from `Hom_A(I^n, M / M_n)` to sections on
`Spec A ∖ V(I)`, built from an explicit finite generating family. -/
noncomputable def idealPowerQuotientHomToComplementSectionsStageMapUsing
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    I.powerQuotientHomModuleStage M n ⟶ idealComplementTildeSections I M :=
  IdealComplementStage.IsLinear.stageMap
    (idealPowerQuotientHomStageUsing G M)
    (idealPowerQuotientHomStageUsing_isLinear G M)
    n

/-- Applying the linear quotient stage comparison map gives the section defined by the local
fraction formula. -/
@[simp]
theorem idealPowerQuotientHomToComplementSectionsStageMapUsing_apply
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ)
    (φ : I.powerQuotientHom M n) :
    (idealPowerQuotientHomToComplementSectionsStageMapUsing G M n).hom φ =
      idealPowerQuotientHomSectionAtStageUsing G M n φ := sorry

/-- The stagewise quotient comparison maps commute with their direct-system transition maps. -/
theorem idealPowerQuotientHomToComplementSectionsStageMapUsing_naturality
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    I.powerQuotientHomModuleTransition M n ≫
        idealPowerQuotientHomToComplementSectionsStageMapUsing G M (n + 1) =
      idealPowerQuotientHomToComplementSectionsStageMapUsing G M n := sorry

/-- The stagewise quotient Hom comparison maps are natural in a morphism of `A`-modules. -/
theorem idealPowerQuotientHomToComplementSectionsStageMapUsing_module_naturality
    (G : I.FiniteGeneratingFamily) {M N : ModuleCat A} (f : M ⟶ N) (n : ℕ) :
    I.powerQuotientHomModuleStageMap f.hom n ≫
        idealPowerQuotientHomToComplementSectionsStageMapUsing G N n =
      idealPowerQuotientHomToComplementSectionsStageMapUsing G M n ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The comparison map from the sequential colimit of `Hom_A(I^n, M / M_n)` to sections on
`Spec A ∖ V(I)`, built from an explicit finite generating family. -/
noncomputable def idealPowerQuotientHomColimitToComplementSectionsUsing
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) :
    colimit (I.powerQuotientHomModuleDiagram M) ⟶ idealComplementTildeSections I M :=
  IdealComplementStage.IsLinear.colimitMap
    (idealPowerQuotientHomStageUsing G M)
    (idealPowerQuotientHomStageUsing_isLinear G M)

/-- The quotient colimit comparison map induced by `G` computes to its stagewise comparison map
on every colimit inclusion. -/
@[reassoc]
theorem idealPowerQuotientHomColimitToComplementSectionsUsing_ι
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    colimit.ι (I.powerQuotientHomModuleDiagram M) n ≫
        idealPowerQuotientHomColimitToComplementSectionsUsing G M =
      idealPowerQuotientHomToComplementSectionsStageMapUsing G M n := sorry

/-- The quotient Hom colimit comparison maps are natural in a morphism of `A`-modules. -/
theorem idealPowerQuotientHomColimitToComplementSectionsUsing_module_naturality
    (G : I.FiniteGeneratingFamily) {M N : ModuleCat A} (f : M ⟶ N) :
    colim.map (I.powerQuotientHomModuleDiagramMap f.hom) ≫
        idealPowerQuotientHomColimitToComplementSectionsUsing G N =
      idealPowerQuotientHomColimitToComplementSectionsUsing G M ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The stagewise quotient Hom comparison map is independent of the finite generating family
used to construct it. -/
theorem idealPowerQuotientHomToComplementSectionsStageMapUsing_eq
    (G H : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientHomToComplementSectionsStageMapUsing G M n =
      idealPowerQuotientHomToComplementSectionsStageMapUsing H M n := sorry

/-- The quotient Hom colimit comparison map is independent of the finite generating family used
to construct it. -/
theorem idealPowerQuotientHomColimitToComplementSectionsUsing_eq
    (G H : I.FiniteGeneratingFamily) (M : ModuleCat A) :
    idealPowerQuotientHomColimitToComplementSectionsUsing G M =
      idealPowerQuotientHomColimitToComplementSectionsUsing H M := sorry

/-- The stagewise quotient Hom comparison map obtained from a finite-generation witness for `I`. -/
noncomputable def idealPowerQuotientHomToComplementSectionsStageMap (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) (n : ℕ) :
    I.powerQuotientHomModuleStage M n ⟶ idealComplementTildeSections I M :=
  idealPowerQuotientHomToComplementSectionsStageMapUsing
    (Ideal.FiniteGeneratingFamily.ofFG I hI) M n

/-- The convenience stagewise quotient Hom comparison map agrees with the construction using any
explicit finite generating family of `I`. -/
theorem idealPowerQuotientHomToComplementSectionsStageMap_eq_using
    (I : Ideal A) (hI : I.FG) (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientHomToComplementSectionsStageMap I hI M n =
      idealPowerQuotientHomToComplementSectionsStageMapUsing G M n := sorry

/-- The convenience stagewise quotient Hom comparison maps commute with the direct-system
transitions. -/
theorem idealPowerQuotientHomToComplementSectionsStageMap_naturality
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) (n : ℕ) :
    I.powerQuotientHomModuleTransition M n ≫
        idealPowerQuotientHomToComplementSectionsStageMap I hI M (n + 1) =
      idealPowerQuotientHomToComplementSectionsStageMap I hI M n := sorry

/-- The convenience stagewise quotient Hom comparison maps are natural in a morphism of
`A`-modules. -/
theorem idealPowerQuotientHomToComplementSectionsStageMap_module_naturality
    (I : Ideal A) (hI : I.FG) {M N : ModuleCat A} (f : M ⟶ N) (n : ℕ) :
    I.powerQuotientHomModuleStageMap f.hom n ≫
        idealPowerQuotientHomToComplementSectionsStageMap I hI N n =
      idealPowerQuotientHomToComplementSectionsStageMap I hI M n ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The canonical comparison map
`colim_n Hom_A(I^n, M / M_n) → Γ(Spec A ∖ V(I), tilde M)`. -/
noncomputable def idealPowerQuotientHomColimitToComplementSections (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) :
    colimit (I.powerQuotientHomModuleDiagram M) ⟶ idealComplementTildeSections I M :=
  idealPowerQuotientHomColimitToComplementSectionsUsing
    (Ideal.FiniteGeneratingFamily.ofFG I hI) M

/-- The convenience quotient Hom comparison map agrees with the construction using any explicit
finite generating family of `I`. -/
theorem idealPowerQuotientHomColimitToComplementSections_eq_using (I : Ideal A) (hI : I.FG)
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) :
    idealPowerQuotientHomColimitToComplementSections I hI M =
      idealPowerQuotientHomColimitToComplementSectionsUsing G M := sorry

/-- The canonical quotient-Hom comparison map does not depend on the chosen finite-generation
proof for `I`. -/
theorem idealPowerQuotientHomColimitToComplementSections_eq_of_fg (I : Ideal A)
    {hI hI' : I.FG} (M : ModuleCat A) :
    idealPowerQuotientHomColimitToComplementSections I hI M =
      idealPowerQuotientHomColimitToComplementSections I hI' M := sorry

/-- The stagewise canonical quotient-Hom comparison map does not depend on the finite-generation
proof for `I`. -/
theorem idealPowerQuotientHomToComplementSectionsStageMap_eq_of_fg (I : Ideal A)
    {hI hI' : I.FG} (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientHomToComplementSectionsStageMap I hI M n =
      idealPowerQuotientHomToComplementSectionsStageMap I hI' M n := sorry

/-- The canonical quotient Hom colimit comparison map is natural in a morphism of `A`-modules. -/
theorem idealPowerQuotientHomColimitToComplementSections_module_naturality
    (I : Ideal A) (hI : I.FG) {M N : ModuleCat A} (f : M ⟶ N) :
    colim.map (I.powerQuotientHomModuleDiagramMap f.hom) ≫
        idealPowerQuotientHomColimitToComplementSections I hI N =
      idealPowerQuotientHomColimitToComplementSections I hI M ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The canonical quotient Hom comparison map restricts to the stage map on every colimit
inclusion. -/
@[reassoc]
theorem idealPowerQuotientHomColimitToComplementSections_ι (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) (n : ℕ) :
    colimit.ι (I.powerQuotientHomModuleDiagram M) n ≫
        idealPowerQuotientHomColimitToComplementSections I hI M =
      idealPowerQuotientHomToComplementSectionsStageMap I hI M n := sorry

end AlgebraicGeometry.Scheme.Modules

