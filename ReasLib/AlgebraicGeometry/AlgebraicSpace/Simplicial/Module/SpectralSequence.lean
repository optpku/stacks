/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- An fppf hypercovering yields spectral sequences functorially in quasi-coherent
module coefficients, with natural first-page comparisons and convergence to the
cohomology of the augmentation target. -/
theorem qcohEtaleSpectralSequence_functorial (ha : IsFppfHypercovering a) :
    ∃ (E : (spacesQuasiCoherentModuleProperty X).FullSubcategory ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory)
          (p q : ℕ),
        ((E.obj F).page 1 le_rfl).X (p, q) ≅ stageModuleCohomology a F.obj p q),
      (∀ F : (spacesQuasiCoherentModuleProperty X).FullSubcategory,
        CohomologicalSpectralSequenceNat.ConvergesTo (E.obj F)
          (spacesEtaleModuleCohomology X F.obj)) ∧
      (∀ {F G : (spacesQuasiCoherentModuleProperty X).FullSubcategory}
          (f : F ⟶ G) (p q : ℕ),
        (pageOneIso F p q).inv ≫ ((E.map f).hom 1 le_rfl).f (p, q) ≫
            (pageOneIso G p q).hom =
          (stageModuleCohomologyFunctor a p q).map
            ((spacesQuasiCoherentModuleProperty X).ι.map f)) := sorry

/-- An fppf hypercovering of an algebraic space gives a first-quadrant spectral
sequence whose first page is the étale cohomology of the pulled-back quasi-coherent
module on each stage and whose abutment is its étale cohomology on the target. -/
@[stacks 0DHH]
theorem exists_qcohEtaleSpectralSequence (ha : IsFppfHypercovering a)
    (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ stageModuleCohomology a F.obj p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (spacesEtaleModuleCohomology X F.obj) := by
  obtain ⟨E, pageOneIso, hconverges, hnaturality⟩ :=
    qcohEtaleSpectralSequence_functorial a ha
  exact ⟨E.obj F, pageOneIso F, hconverges F⟩

end AlgebraicGeometry.AlgebraicSpace.Simplicial
