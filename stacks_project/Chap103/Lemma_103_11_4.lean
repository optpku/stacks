/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap103.Proposition_103_11_7_Pushforward

/-!
# Quasi-coherent Leray spectral sequence for algebraic stacks

A quasi-compact quasi-separated 1-morphism of algebraic stacks yields a Leray
spectral sequence whose `E₂`-page is cohomology of quasi-coherent higher
direct images, abutting to cohomology of the original quasi-coherent sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The cohomology group `H^n(𝒳, F)` of a quasi-coherent module `F`, computed as
fppf abelian sheaf cohomology of the carrier-lifted underlying module. -/
noncomputable abbrev qcohCohomology (X : GroupoidsOver S) (F : QCoh X) (n : ℕ)
    [HasSheafify (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (fppfRingedSite X).siteTopology n).obj
    ((SheafOfModules.toSheaf (fppfRingedSite X).structureSheaf).obj
      (RingedSite.Module.carrierLift (fppfRingedSite X) ((QCoh.inclusion X).obj F)))

/-- `qcohCohomology X F n` is fppf abelian sheaf cohomology of the
carrier-lifted underlying module of `F`. -/
theorem qcohCohomology_eq (X : GroupoidsOver S) (F : QCoh X) (n : ℕ)
    [HasSheafify (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1})] :
    qcohCohomology X F n =
      (Sheaf.functorH (fppfRingedSite X).siteTopology n).obj
        ((SheafOfModules.toSheaf (fppfRingedSite X).structureSheaf).obj
          (RingedSite.Module.carrierLift (fppfRingedSite X)
            ((QCoh.inclusion X).obj F))) :=
  rfl

/-- The displayed `E₂^{p, q}` object `H^p(𝒴, R^q f_{QCoh,*} F)` of the
quasi-coherent Leray spectral sequence. -/
noncomputable abbrev qcohLerayPageTwo {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (p q : ℕ)
    [HasSheafify (fppfRingedSite Y).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (fppfRingedSite Y).siteTopology AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  qcohCohomology Y (qCohHigherDirectImage f F q) p

/-- `qcohLerayPageTwo f F p q` is `qcohCohomology` of `R^q f_{QCoh,*} F`. -/
theorem qcohLerayPageTwo_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (p q : ℕ)
    [HasSheafify (fppfRingedSite Y).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (fppfRingedSite Y).siteTopology AddCommGrpCat.{u + 1})] :
    qcohLerayPageTwo f F p q =
      qcohCohomology Y (qCohHigherDirectImage f F q) p :=
  rfl

/-- Lemma 103.11.4: Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated
1-morphism of algebraic stacks, and let `F` be a quasi-coherent sheaf on `𝒳`.
Then there exists a spectral sequence with `E₂^{p, q} = H^p(𝒴, R^q f_{QCoh,*} F)`
converging to `H^{p+q}(𝒳, F)`. The displayed page is `qcohLerayPageTwo f F p q`
and the abutment is `qcohCohomology X F`. -/
@[stacks 0782]
theorem exists_qcohLeraySpectralSequence {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (F : QCoh X)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSheafify (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u + 1})]
    [HasSheafify (fppfRingedSite Y).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (fppfRingedSite Y).siteTopology AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 2)
      (pageTwoIso : ∀ p q : ℕ,
        (E.page 2 le_rfl).X (p, q) ≅ qcohLerayPageTwo f F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ qcohCohomology X F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
