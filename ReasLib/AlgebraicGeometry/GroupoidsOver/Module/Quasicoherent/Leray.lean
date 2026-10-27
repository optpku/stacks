/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Cohomology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment

/-! # The quasi-coherent Leray spectral sequence -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- A quasi-compact quasi-separated morphism of algebraic stacks admits a
first-quadrant Leray spectral sequence with second page
`H^p(Y, R^q f_{QCoh,*} F)`, converging to `H^{p + q}(X, F)`. -/
theorem exists_leraySpectralSequence {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (F : QCoh X)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSheafify (ringedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (ringedSite X).siteTopology AddCommGrpCat.{u + 1})]
    [HasSheafify (ringedSite Y).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (ringedSite Y).siteTopology AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 2)
      (pageTwoIso : ∀ p q : ℕ,
        (E.page 2 le_rfl).X (p, q) ≅ QCoh.cohomology Y (qCohHigherDirectImage f F q) p),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ QCoh.cohomology X F n) := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
