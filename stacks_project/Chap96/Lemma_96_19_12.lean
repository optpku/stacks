/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Cech.ModulePushforwardSpectralSequence
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u

/- Lemma 96.19.12: A faithful morphism whose essential image covers locally and
whose source has equalizers yields the relative Čech-to-pushforward spectral
sequence of module sheaves for every standard topology. -/
@[stacks 072E] #check
  (AlgebraicGeometry.GroupoidsOver.exists_relativeCechModulePushforwardSpectralSequence :
    ∀ {S : Scheme.{u}} {U X Y : GroupoidsOver S} (f : U ⟶ X) (g : X ⟶ Y)
      (τ : StandardTopology)
      (F : SheafOfModules.{u + 1} (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf X τ))
      (hf : AlgebraicGeometry.GroupoidsOver.coversByEssentialImage f τ)
      [HasEqualizers U.total] [Functor.Faithful (toFunctor f)],
      ∃ (E : CohomologicalSpectralSequenceNat
          (SheafOfModules.{u + 1}
            (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf Y τ)) 1)
        (pageOneIso : ∀ p q : ℕ,
          (E.page 1 le_rfl).X (p, q) ≅
            AlgebraicGeometry.GroupoidsOver.associatedModuleHigherDirectImage
              (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g) τ
              (AlgebraicGeometry.GroupoidsOver.relativeCechModuleInverseImage f τ F p) q),
        CohomologicalSpectralSequenceNat.ConvergesTo E
          (fun n ↦ AlgebraicGeometry.GroupoidsOver.associatedModuleHigherDirectImage g τ F n))
