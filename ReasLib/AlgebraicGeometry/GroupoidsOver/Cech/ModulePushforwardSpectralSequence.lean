/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pushforward
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.ModuleSpectralSequence

/-!
# The relative Čech spectral sequence for module pushforward

The covering simplices compute higher direct images of module sheaves through a
first-quadrant spectral sequence in the module-sheaf category of the final target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- The first-page object `R^q (g ∘ f_p)_* f_p⁻¹ F` of the relative Čech module
pushforward spectral sequence, as a sheaf of modules on `𝒴_τ`. -/
noncomputable abbrev relativeCechModulePushforwardPageOne (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (p q : ℕ)
    [HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ))] :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  associatedModuleHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
    (relativeCechModuleInverseImage f τ F p) q

/-- Unfolding of `relativeCechModulePushforwardPageOne` as a module-valued higher
direct image of `f_p⁻¹ F` along `g ∘ f_p`. -/
theorem relativeCechModulePushforwardPageOne_obj (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (p q : ℕ)
    [HasInjectiveResolutions
      (SheafOfModules.{u + 1}
        (associatedStructureSheaf (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌) τ))] :
    relativeCechModulePushforwardPageOne f g τ F p q =
      associatedModuleHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
        (relativeCechModuleInverseImage f τ F p) q :=
  rfl

/-- A faithful, locally essentially covering morphism with source equalizers yields
a first-quadrant spectral sequence of module sheaves. Its first page consists of
higher direct images of inverse images on covering simplices, and it converges
to the higher direct images of the coefficient sheaf. -/
theorem exists_relativeCechModulePushforwardSpectralSequence (f : U ⟶ X) (g : X ⟶ Y)
    (τ : StandardTopology) (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (hf : coversByEssentialImage f τ)
    [HasEqualizers U.total] [Functor.Faithful (toFunctor f)] :
    ∃ (E : CohomologicalSpectralSequenceNat
        (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          associatedModuleHigherDirectImage
            (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
            (relativeCechModuleInverseImage f τ F p) q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ associatedModuleHigherDirectImage g τ F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
