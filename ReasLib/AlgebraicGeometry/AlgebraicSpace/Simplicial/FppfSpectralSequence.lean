/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment

/-!
# Étale cohomology spectral sequences for fppf hypercoverings

An fppf hypercovering of an algebraic space gives a first-quadrant spectral
sequence from the étale cohomology of its stages to the étale cohomology of
its augmentation target, functorially in abelian coefficient sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The étale cohomology spectral sequences of an fppf hypercovering can be
chosen functorially in abelian coefficient sheaves, with natural first-page
comparisons and convergence to the cohomology of the augmentation target. -/
theorem etaleSpectralSequence_functorial (ha : IsFppfHypercovering a) :
    ∃ (E : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
          (p q : ℕ),
        ((E.obj F).page 1 le_rfl).X (p, q) ≅
          (pageOneFunctorNonneg a p (q : ℤ)).obj F),
      (∀ F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1},
        CohomologicalSpectralSequenceNat.ConvergesTo (E.obj F)
          (fun n : ℕ ↦ (plusCohomology X (n : ℤ)).obj F)) ∧
      (∀ {F G : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}}
          (f : F ⟶ G) (p q : ℕ),
        (pageOneIso F p q).inv ≫ ((E.map f).hom 1 le_rfl).f (p, q) ≫
            (pageOneIso G p q).hom = (pageOneFunctorNonneg a p (q : ℤ)).map f) := sorry

/-- An fppf hypercovering of an algebraic space yields a convergent
first-quadrant spectral sequence for every abelian étale sheaf, whose first
page is the étale cohomology of the stage pullbacks and whose total-degree
abutment is the étale cohomology of the augmentation target. -/
theorem exists_etaleSpectralSequence (ha : IsFppfHypercovering a)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          (plusCohomology (U.obj (op ⦋p⦌)) (q : ℤ)).obj ((pullbackStage a p).obj F)),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n : ℕ ↦ (plusCohomology X (n : ℤ)).obj F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial
