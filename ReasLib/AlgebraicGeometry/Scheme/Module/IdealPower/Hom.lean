/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.ModuleCat
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Comparison

/-!
# Hom-to-sections comparison over an affine ideal complement

The core API is parameterized by an explicit finite generating family of the
ideal.  The `I.FG` convenience maps select such a family only at the outermost
boundary, so downstream arguments can retain their own cover data when needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry PrimeSpectrum
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The local section on the `i`-th basic open associated to a map `I^n →ₗ[A] M`, using an
explicit finite generating family of `I`. -/
noncomputable def idealPowerHomLocalSectionUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerHom M n) (i : G.Index) :
    ((tildePresheaf M).obj (Opposite.op (G.basicOpen i)) : Type u) :=
  tildeBasicOpenPowerSection M (G.generator i) n
    (φ ⟨(G.generator i) ^ n, Ideal.pow_mem_pow (G.generator_mem i) n⟩)

/-- The local fractions associated to an ideal-power Hom map are compatible on the chosen basic
open cover. -/
theorem idealPowerHomLocalSectionUsing_compatible (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerHom M n) :
    TopCat.Presheaf.IsCompatible
      (tildePresheaf M)
      G.basicOpen
      (idealPowerHomLocalSectionUsing G M n φ) := sorry

/-- The finite-cover stage data for the ideal-power Hom comparison.  This records only the
concrete local-fraction formula and its compatibility; gluing and colimit descent are supplied
by `IdealComplementStage`. -/
noncomputable def idealPowerHomStageUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) : IdealComplementStage G M where
  stage := I.powerHomModuleStage M
  transition := fun n ↦ I.powerHomModuleTransition M n
  localSection := fun n φ i ↦ idealPowerHomLocalSectionUsing G M n φ i
  compatible := fun n φ ↦ idealPowerHomLocalSectionUsing_compatible G M n φ

/-- The canonical glued sections of the ideal-power Hom stage are linear and commute with
the stage transitions. -/
theorem idealPowerHomStageUsing_isLinear (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) : (idealPowerHomStageUsing G M).IsLinear := sorry

/-- The section of `tilde M` on `Spec A ∖ V(I)` induced at one Hom stage, using an explicit
finite generating family. -/
noncomputable def idealPowerHomSectionAtStageUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerHom M n) :
    idealComplementTildeSections I M :=
  (idealPowerHomStageUsing G M).gluedSection n φ

/-- Restricting the stagewise Hom section to a chosen basic open gives its prescribed fraction. -/
theorem idealPowerHomSectionAtStageUsing_spec (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) (φ : I.powerHom M n) (i : G.Index) :
    (tildePresheaf M).map (homOfLE (G.basicOpen_le_idealComplementOpens i)).op
        (idealPowerHomSectionAtStageUsing G M n φ) =
      idealPowerHomLocalSectionUsing G M n φ i := sorry

/-- The stagewise comparison map from `Hom_A(I^n, M)` to sections on `Spec A ∖ V(I)`, built
from an explicit finite generating family. -/
noncomputable def idealPowerHomToComplementSectionsStageMapUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) :
    I.powerHomModuleStage M n ⟶ idealComplementTildeSections I M :=
  IdealComplementStage.IsLinear.stageMap
    (idealPowerHomStageUsing G M)
    (idealPowerHomStageUsing_isLinear G M)
    n

/-- Applying the linear stage comparison map gives the section defined by the local-fraction
formula. -/
@[simp]
theorem idealPowerHomToComplementSectionsStageMapUsing_apply
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) (φ : I.powerHom M n) :
    (idealPowerHomToComplementSectionsStageMapUsing G M n).hom φ =
      idealPowerHomSectionAtStageUsing G M n φ := sorry

/-- The stagewise Hom comparison maps commute with the direct-system transition maps. -/
theorem idealPowerHomToComplementSectionsStageMapUsing_naturality
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    I.powerHomModuleTransition M n ≫
        idealPowerHomToComplementSectionsStageMapUsing G M (n + 1) =
      idealPowerHomToComplementSectionsStageMapUsing G M n := sorry

/-- The stagewise Hom comparison maps are natural in a morphism of `A`-modules. -/
theorem idealPowerHomToComplementSectionsStageMapUsing_module_naturality
    (G : I.FiniteGeneratingFamily) {M N : ModuleCat A} (f : M ⟶ N) (n : ℕ) :
    I.powerHomModuleStageMap f.hom n ≫
        idealPowerHomToComplementSectionsStageMapUsing G N n =
      idealPowerHomToComplementSectionsStageMapUsing G M n ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The comparison map from the sequential colimit of `Hom_A(I^n, M)` to sections on
`Spec A ∖ V(I)`, built from an explicit finite generating family. -/
noncomputable def idealPowerHomColimitToComplementSectionsUsing (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) :
    colimit (I.powerHomModuleDiagram M) ⟶ idealComplementTildeSections I M :=
  IdealComplementStage.IsLinear.colimitMap
    (idealPowerHomStageUsing G M)
    (idealPowerHomStageUsing_isLinear G M)

/-- The colimit comparison map induced by `G` computes to its stagewise comparison map on every
colimit inclusion. -/
@[reassoc]
theorem idealPowerHomColimitToComplementSectionsUsing_ι (G : I.FiniteGeneratingFamily)
    (M : ModuleCat A) (n : ℕ) :
    colimit.ι (I.powerHomModuleDiagram M) n ≫
        idealPowerHomColimitToComplementSectionsUsing G M =
      idealPowerHomToComplementSectionsStageMapUsing G M n := sorry

/-- The Hom colimit comparison maps are natural in a morphism of `A`-modules. -/
theorem idealPowerHomColimitToComplementSectionsUsing_module_naturality
    (G : I.FiniteGeneratingFamily) {M N : ModuleCat A} (f : M ⟶ N) :
    colim.map (I.powerHomModuleDiagramMap f.hom) ≫
        idealPowerHomColimitToComplementSectionsUsing G N =
      idealPowerHomColimitToComplementSectionsUsing G M ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The stagewise Hom comparison map is independent of the finite generating family used to
construct it. -/
theorem idealPowerHomToComplementSectionsStageMapUsing_eq
    (G H : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    idealPowerHomToComplementSectionsStageMapUsing G M n =
      idealPowerHomToComplementSectionsStageMapUsing H M n := sorry

/-- The Hom colimit comparison map is independent of the finite generating family used to
construct it. -/
theorem idealPowerHomColimitToComplementSectionsUsing_eq
    (G H : I.FiniteGeneratingFamily) (M : ModuleCat A) :
    idealPowerHomColimitToComplementSectionsUsing G M =
      idealPowerHomColimitToComplementSectionsUsing H M := sorry

/-- The stagewise Hom comparison map obtained from a finite-generation witness for `I`. -/
noncomputable def idealPowerHomToComplementSectionsStageMap (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) (n : ℕ) :
    I.powerHomModuleStage M n ⟶ idealComplementTildeSections I M :=
  idealPowerHomToComplementSectionsStageMapUsing
    (Ideal.FiniteGeneratingFamily.ofFG I hI) M n

/-- The convenience stagewise Hom comparison map agrees with the construction using any explicit
finite generating family of `I`. -/
theorem idealPowerHomToComplementSectionsStageMap_eq_using (I : Ideal A) (hI : I.FG)
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) (n : ℕ) :
    idealPowerHomToComplementSectionsStageMap I hI M n =
      idealPowerHomToComplementSectionsStageMapUsing G M n := sorry

/-- The convenience stagewise Hom comparison maps commute with the direct-system transitions. -/
theorem idealPowerHomToComplementSectionsStageMap_naturality (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) (n : ℕ) :
    I.powerHomModuleTransition M n ≫ idealPowerHomToComplementSectionsStageMap I hI M (n + 1) =
      idealPowerHomToComplementSectionsStageMap I hI M n := sorry

/-- The convenience stagewise Hom comparison maps are natural in a morphism of `A`-modules. -/
theorem idealPowerHomToComplementSectionsStageMap_module_naturality
    (I : Ideal A) (hI : I.FG) {M N : ModuleCat A} (f : M ⟶ N) (n : ℕ) :
    I.powerHomModuleStageMap f.hom n ≫ idealPowerHomToComplementSectionsStageMap I hI N n =
      idealPowerHomToComplementSectionsStageMap I hI M n ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The canonical comparison map
`colim_n Hom_A(I^n, M) → Γ(Spec A ∖ V(I), tilde M)`. -/
noncomputable def idealPowerHomColimitToComplementSections (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) :
    colimit (I.powerHomModuleDiagram M) ⟶ idealComplementTildeSections I M :=
  idealPowerHomColimitToComplementSectionsUsing
    (Ideal.FiniteGeneratingFamily.ofFG I hI) M

/-- The convenience Hom comparison map agrees with the construction using any explicit finite
generating family of `I`. -/
theorem idealPowerHomColimitToComplementSections_eq_using (I : Ideal A) (hI : I.FG)
    (G : I.FiniteGeneratingFamily) (M : ModuleCat A) :
    idealPowerHomColimitToComplementSections I hI M =
      idealPowerHomColimitToComplementSectionsUsing G M := sorry

/-- The canonical Hom comparison map does not depend on which proof of finite generation is used.
The explicit proof remains an input at construction sites so no arbitrary global witness is chosen. -/
theorem idealPowerHomColimitToComplementSections_eq_of_fg (I : Ideal A)
    {hI hI' : I.FG} (M : ModuleCat A) :
    idealPowerHomColimitToComplementSections I hI M =
      idealPowerHomColimitToComplementSections I hI' M := sorry

/-- The stagewise canonical Hom comparison map does not depend on the finite-generation proof. -/
theorem idealPowerHomToComplementSectionsStageMap_eq_of_fg (I : Ideal A)
    {hI hI' : I.FG} (M : ModuleCat A) (n : ℕ) :
    idealPowerHomToComplementSectionsStageMap I hI M n =
      idealPowerHomToComplementSectionsStageMap I hI' M n := sorry

/-- The canonical Hom colimit comparison map is natural in a morphism of `A`-modules. -/
theorem idealPowerHomColimitToComplementSections_module_naturality
    (I : Ideal A) (hI : I.FG) {M N : ModuleCat A} (f : M ⟶ N) :
    colim.map (I.powerHomModuleDiagramMap f.hom) ≫
        idealPowerHomColimitToComplementSections I hI N =
      idealPowerHomColimitToComplementSections I hI M ≫
        idealComplementTildeSectionsMap I f := sorry

/-- The canonical Hom comparison map restricts to the stage map on every colimit inclusion. -/
@[reassoc]
theorem idealPowerHomColimitToComplementSections_ι (I : Ideal A) (hI : I.FG)
    (M : ModuleCat A) (n : ℕ) :
    colimit.ι (I.powerHomModuleDiagram M) n ≫
        idealPowerHomColimitToComplementSections I hI M =
      idealPowerHomToComplementSectionsStageMap I hI M n := sorry

end AlgebraicGeometry.Scheme.Modules

