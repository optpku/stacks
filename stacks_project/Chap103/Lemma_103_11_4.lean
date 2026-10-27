/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Leray
import StacksCheckRecall

/-! # Quasi-coherent Leray spectral sequence for algebraic stacks -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

/- Lemma 103.11.4: A quasi-compact quasi-separated morphism of algebraic stacks
admits a Leray spectral sequence with second page `H^p(Y, R^q f_{QCoh,*} F)`,
converging to `H^{p + q}(X, F)`. -/
@[stacks 0782] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.exists_leraySpectralSequence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (F : GroupoidsOver.QCoh X)
      [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
      [HasSheafify (GroupoidsOver.ringedSite X).siteTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1}
        (Sheaf (GroupoidsOver.ringedSite X).siteTopology AddCommGrpCat.{u + 1})]
      [HasSheafify (GroupoidsOver.ringedSite Y).siteTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1}
        (Sheaf (GroupoidsOver.ringedSite Y).siteTopology AddCommGrpCat.{u + 1})],
      ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 2)
        (pageTwoIso : ∀ p q : ℕ,
          (E.page 2 le_rfl).X (p, q) ≅
            GroupoidsOver.QCoh.cohomology Y (GroupoidsOver.qCohHigherDirectImage f F q) p),
        CohomologicalSpectralSequenceNat.ConvergesTo E
          (fun n ↦ GroupoidsOver.QCoh.cohomology X F n))
