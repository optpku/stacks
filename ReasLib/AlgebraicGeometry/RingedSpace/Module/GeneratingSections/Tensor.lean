/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Presentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratingSections.Stalk
public import ReasLib.Algebra.Module.TensorProduct.Generators
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generating sections of tensor products

This file separates the algebraic spanning lemma, the compatibility of tensor sections with
germs, and the resulting family of global generators.  The construction uses the canonical
tensor product and stalk comparison for module sheaves on a ringed space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Tensor.Stalk

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The tensor-stalk comparison sends the germ of a global pure tensor section to the pure
tensor of the two germs. -/
theorem comparison_germ_tensorSection
    (F G : X.Modules) (x : X) (s : F.sections) (t : G.sections) :
    comparison F G x
        (Γgerm (tensorObj F G).val.presheaf x
          (RingedSpace.sectionsEquivTop (tensorObj F G)
            (RingedSpace.tensorSection s t))) =
      Γgerm F.val.presheaf x (RingedSpace.sectionsEquivTop F s) ⊗ₜ[X.presheaf.stalk x]
        Γgerm G.val.presheaf x (RingedSpace.sectionsEquivTop G t) := by
  exact comparison_germ_tensorSectionOver F G x ⊤ (by trivial)
    (RingedSpace.sectionsEquivTop F s) (RingedSpace.sectionsEquivTop G t)

end AlgebraicGeometry.RingedSpace.Tensor.Stalk

namespace SheafOfModules.GeneratingSections

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {F G : X.Modules}

/-- After the tensor-stalk comparison, the germs of the pairwise tensor sections span the
tensor product of the two stalk modules. -/
theorem tensor_comparison_span_eq_top
    (σ : F.GeneratingSections) (τ : G.GeneratingSections) (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun ij : σ.I × τ.I ↦
        RingedSpace.Tensor.Stalk.comparison F G x
          (Γgerm (tensorObj F G).val.presheaf x
            (RingedSpace.sectionsEquivTop (tensorObj F G)
              (RingedSpace.tensorSection (σ.s ij.1) (τ.s ij.2))))) = ⊤ := by
  simp_rw [RingedSpace.Tensor.Stalk.comparison_germ_tensorSection]
  exact TensorProduct.span_range_tmul_eq_top
    (M := RingedSpace.stalkModuleCat F x) (N := RingedSpace.stalkModuleCat G x)
    (fun i ↦ Γgerm F.val.presheaf x (RingedSpace.sectionsEquivTop F (σ.s i)))
    (fun j ↦ Γgerm G.val.presheaf x (RingedSpace.sectionsEquivTop G (τ.s j)))
    (CommRing.stalkSpan_eq_top (𝒪 := X.sheaf) σ x)
    (CommRing.stalkSpan_eq_top (𝒪 := X.sheaf) τ x)

/-- The germs of the pairwise tensor sections of two generating families span every stalk of
the tensor-product module sheaf. -/
theorem tensor_stalkwise_span_eq_top
    (σ : F.GeneratingSections) (τ : G.GeneratingSections) :
    ∀ x : X,
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun ij : σ.I × τ.I ↦
          Γgerm (tensorObj F G).val.presheaf x
            (RingedSpace.sectionsEquivTop (tensorObj F G)
              (RingedSpace.tensorSection (σ.s ij.1) (τ.s ij.2)))) = ⊤ := by
  intro x
  let e := (RingedSpace.Tensor.Stalk.comparisonIso F G x).toLinearEquiv
  apply Submodule.map_injective_of_injective e.injective
  erw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective]
  exact tensor_comparison_span_eq_top σ τ x

/-- The free morphism classified by all pairwise tensor sections of two generating families is
an epimorphism. -/
theorem tensor_epi (σ : F.GeneratingSections) (τ : G.GeneratingSections) :
    Epi ((tensorObj F G).freeHomEquiv.symm
      (fun ij : σ.I × τ.I ↦
        RingedSpace.tensorSection (σ.s ij.1) (τ.s ij.2))) := by
  exact (CommRing.epi_iff_stalkSpan_eq_top (𝒪 := X.sheaf) _).mpr
    (tensor_stalkwise_span_eq_top σ τ)

/-- Lemma 17.4.3 (01AO): pairwise pure tensors of two chosen families of global generators form
a family of global generators for the tensor product. -/
@[stacks 01AO "tensor products of globally generated modules"]
noncomputable def tensor (σ : F.GeneratingSections) (τ : G.GeneratingSections) :
    (tensorObj F G).GeneratingSections where
  I := σ.I × τ.I
  s ij := RingedSpace.tensorSection (σ.s ij.1) (τ.s ij.2)
  epi := tensor_epi σ τ

/-- Tensoring finite chosen families of global generators gives a finite family of global
generators. -/
instance tensor_isFiniteType
    (σ : F.GeneratingSections) (τ : G.GeneratingSections)
    [σ.IsFiniteType] [τ.IsFiniteType] : (tensor σ τ).IsFiniteType := by
  exact ⟨inferInstanceAs (Finite (σ.I × τ.I))⟩

/-- Lemma 17.4.3 (01AO): a tensor product of module sheaves generated by global sections is
generated by global sections. -/
@[stacks 01AO "global generation is closed under tensor products"]
theorem nonempty_tensor
    (hF : Nonempty F.GeneratingSections) (hG : Nonempty G.GeneratingSections) :
    Nonempty (tensorObj F G).GeneratingSections := by
  obtain ⟨σ⟩ := hF
  obtain ⟨τ⟩ := hG
  exact ⟨tensor σ τ⟩

end SheafOfModules.GeneratingSections

namespace SheafOfModules.IsGloballyGenerated

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Lemma 17.4.3 (01AO): global generation is closed under tensor products of module sheaves. -/
@[stacks 01AO "property-level tensor closure"]
theorem tensor (F G : X.Modules) [IsGloballyGenerated F] [IsGloballyGenerated G] :
    IsGloballyGenerated (tensorObj F G) := by
  exact GeneratingSections.nonempty_tensor
    ‹IsGloballyGenerated F› ‹IsGloballyGenerated G›

end SheafOfModules.IsGloballyGenerated

namespace SheafOfModules.IsGeneratedBy

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Tensoring sheaves generated by `r` and `s` global sections gives a sheaf generated by
`r * s` global sections. -/
@[stacks 01AO "fixed-number tensor closure"]
theorem tensor (F G : X.Modules) {r s : ℕ} [IsGeneratedBy F r] [IsGeneratedBy G s] :
    IsGeneratedBy (tensorObj F G) (r * s) := by
  obtain ⟨⟨σ, ⟨eσ⟩⟩⟩ :=
    (isGeneratedBy_iff_nonempty_generatingSections_equiv_fin F r).mp inferInstance
  obtain ⟨⟨τ, ⟨eτ⟩⟩⟩ :=
    (isGeneratedBy_iff_nonempty_generatingSections_equiv_fin G s).mp inferInstance
  let e : (GeneratingSections.tensor σ τ).I ≃ ULift.{u} (Fin (r * s)) :=
    (eσ.prodCongr eτ).trans
      ((Equiv.prodCongr Equiv.ulift Equiv.ulift).trans
        (finProdFinEquiv.trans Equiv.ulift.symm))
  exact isGeneratedBy_of_generatingSections_equiv_ulift_fin e

end SheafOfModules.IsGeneratedBy

namespace SheafOfModules.IsFiniteGloballyGenerated

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Finite global generation is closed under tensor products of module sheaves. -/
@[stacks 01AO "finite tensor closure"]
theorem tensor (F G : X.Modules)
    [IsFiniteGloballyGenerated F] [IsFiniteGloballyGenerated G] :
    IsFiniteGloballyGenerated (tensorObj F G) := by
  obtain ⟨r, hr⟩ := IsFiniteGloballyGenerated.exists_num (ℱ := F)
  obtain ⟨s, hs⟩ := IsFiniteGloballyGenerated.exists_num (ℱ := G)
  letI := hr
  letI := hs
  exact ⟨⟨r * s, IsGeneratedBy.tensor F G⟩⟩

end SheafOfModules.IsFiniteGloballyGenerated
