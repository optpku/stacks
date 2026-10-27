/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.CechSpectralSequence
import StacksCheckRecall

/-! # Relative Čech computation of quasi-coherent higher direct images

The pinned source displays the coefficient formula on `E₂`. Its proof invokes
the ordinary Čech sequence of Sheaves on Stacks, Proposition 96.21.1, whose
pinned statement has the same formula on `E₁`, and applies the exact functor
`Q_𝒴`. An exact functor preserves page indices. The check below therefore uses
the canonical Čech `E₁` convention, recording the apparent indexing
inconsistency rather than asserting a page-only renumbering at fixed bidegrees.
-/

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/- Proposition 103.11.7: A relative Čech cover computes quasi-coherent higher
direct images. The checked statement uses the canonical `E₁` convention
explained above for the pinned source's displayed `E₂` formula. -/
@[stacks 0785] #check
  (AlgebraicGeometry.GroupoidsOver.exists_qcohRelativeCechPushforwardSpectralSequence :
    ∀ [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y) (F : QCoh X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g],
    ∃ (E : CohomologicalSpectralSequenceNat (QCoh Y) 1)
      (pageOneIso : ∀ p q,
        (E.page 1 le_rfl).X (p, q) ≅
          qcohRelativeCechPushforwardPageOne f g F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ qCohHigherDirectImage g F n))
