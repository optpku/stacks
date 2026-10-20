/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.CechSpectralSequence
import StacksCheckRecall

/-!
# Cohomology of algebraic stacks via a relative Čech nerve

A smooth surjective 1-morphism of algebraic stacks that is representable by
algebraic spaces computes étale cohomology of an abelian étale sheaf from the
relative Čech nerve. The same holds in the fppf topology for a surjective flat
morphism locally of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/- Proposition 96.20.1 (1): The relative Čech spectral sequence for etale cohomology. -/
@[stacks 06XJ] #check (AlgebraicGeometry.GroupoidsOver.exists_etaleRelativeCechSpectralSequence :
    ∀ [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X)
    (F : Sheaf (X.etaleTopology) AddCommGrpCat.{u + 1})
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Smooth f]
    [HasSheafify (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology StandardTopology.etale) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.etale p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1}
      (Sheaf (relativeCechSite f StandardTopology.etale p) AddCommGrpCat.{u + 1})],
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechPageOne f StandardTopology.etale F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology StandardTopology.etale) n).obj F))

/- Proposition 96.20.1 (2): The relative Čech spectral sequence for fppf cohomology. -/
@[stacks 06XJ] #check (AlgebraicGeometry.GroupoidsOver.exists_fppfRelativeCechSpectralSequence :
    ∀ [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X)
    (F : Sheaf (X.fppfTopology) AddCommGrpCat.{u + 1})
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [HasSheafify (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.fppf p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1}
      (Sheaf (relativeCechSite f StandardTopology.fppf p) AddCommGrpCat.{u + 1})],
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechPageOne f StandardTopology.fppf F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology StandardTopology.fppf) n).obj F))

end AlgebraicGeometry.GroupoidsOver
