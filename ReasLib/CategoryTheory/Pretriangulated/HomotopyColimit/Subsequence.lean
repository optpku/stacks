/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Sequential.Reindex
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Subsequence Invariance of Sequential Homotopy Colimits

This leaf applies the neutral sequential-diagram reindexing API to telescope
presentations. It retains only the subsequence-specific comparison and selected-stage
equations; coproduct, connecting-map, cocone, and triangle computations are inherited
directly from `Presentation.HomWithIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory

namespace HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.Subsequence

/-- A comparison between a telescope presentation of a sequential diagram and one of a
strictly increasing subsequence, as the corresponding specialization of an invertible map of
explicit telescope presentations. -/
@[stacks 0CRJ "comparison of full and subsequence telescope presentations"]
abbrev Comparison {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s)
    {Xfull Xsub : D} (Pfull : Presentation K Xfull)
    (Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub) :=
  Presentation.HomWithIso (SequentialDiagram.toSubsequence K hs) Pfull Psub

namespace Comparison

/-- At every selected index, the full presentation leg followed by the comparison isomorphism
is exactly the corresponding subsequence presentation leg. -/
@[reassoc, stacks 0CRJ]
theorem selectedStage_naturality {K : ℕ ⥤ D} {s : ℕ → ℕ} {hs : StrictMono s}
    {Xfull Xsub : D} {Pfull : Presentation K Xfull}
    {Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub}
    (Φ : Comparison hs Pfull Psub) (n : ℕ) :
    Pfull.ι (s n) ≫ Φ.iso.hom = Psub.ι n := sorry

/-- The inverse comparison carries every subsequence presentation leg back to the full
presentation leg at the selected index. -/
@[reassoc, stacks 0CRJ]
theorem selectedStage_naturality_inv
    {K : ℕ ⥤ D} {s : ℕ → ℕ} {hs : StrictMono s}
    {Xfull Xsub : D} {Pfull : Presentation K Xfull}
    {Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub}
    (Φ : Comparison hs Pfull Psub) (n : ℕ) :
    Psub.ι n ≫ Φ.iso.inv = Pfull.ι (s n) := sorry

end Comparison

/-- Any presentations of a sequential diagram and a strictly increasing subsequence admit a
compatible comparison. -/
@[stacks 0CRJ "comparison of full and subsequence homotopy colimits"]
theorem nonemptyComparison {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s)
    {Xfull Xsub : D} (Pfull : Presentation K Xfull)
    (Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub) :
    Nonempty (Comparison hs Pfull Psub) := sorry

/-- The objects of any presentations of a sequential diagram and a strictly increasing
subsequence are isomorphic, oriented from the full diagram to the subsequence. -/
theorem nonemptyIso {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s)
    {Xfull Xsub : D} (Pfull : Presentation K Xfull)
    (Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub) :
    Nonempty (Xfull ≅ Xsub) := sorry

/-- There is a map from the full presentation to the subsequence presentation compatible with
the aligned components of the canonical full-to-subsequence natural transformation. -/
theorem existsStageMap {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s)
    {Xfull Xsub : D} (Pfull : Presentation K Xfull)
    (Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub) :
    ∃ f : Xfull ⟶ Xsub, ∀ n : ℕ,
      Pfull.ι n ≫ f =
        K.map (homOfLE (hs.le_apply (x := n))) ≫ Psub.ι n := sorry

/-- There is a full-to-subsequence object isomorphism compatible directly with every selected
stage. -/
@[stacks 0CRJ "stage-compatible subsequence isomorphism"]
theorem existsStageIso {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s)
    {Xfull Xsub : D} (Pfull : Presentation K Xfull)
    (Psub : Presentation (SequentialDiagram.subsequence K hs) Xsub) :
    ∃ e : Xfull ≅ Xsub, ∀ n : ℕ,
      Pfull.ι (s n) ≫ e.hom = Psub.ι n := sorry

end Presentation.Subsequence

namespace IsOf

/-- A homotopy-colimit presentation for a sequential diagram also presents the same object as
a homotopy colimit of any strictly increasing subsequence. -/
theorem subsequence {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s) {X : D}
    (h : HomotopyColimit.IsOf K X) :
    HomotopyColimit.IsOf (SequentialDiagram.subsequence K hs) X := sorry

/-- A homotopy-colimit presentation for a strictly increasing subsequence also presents the
same object as a homotopy colimit of the full sequential diagram. -/
theorem ofSubsequence {K : ℕ ⥤ D} {s : ℕ → ℕ} (hs : StrictMono s) {X : D}
    (h : HomotopyColimit.IsOf (SequentialDiagram.subsequence K hs) X) :
    HomotopyColimit.IsOf K X := sorry

/-- Homotopy-colimit objects of a sequential diagram and of a strictly increasing subsequence
are nonemptily isomorphic, oriented from the full diagram to the subsequence. -/
theorem nonemptyIsoToSubsequence (K : ℕ ⥤ D) {s : ℕ → ℕ} (hs : StrictMono s)
    {Xfull Xsub : D} (hfull : HomotopyColimit.IsOf K Xfull)
    (hsub : HomotopyColimit.IsOf (SequentialDiagram.subsequence K hs) Xsub) :
    Nonempty (Xfull ≅ Xsub) := sorry

/-- Homotopy colimits of a sequential diagram and of any strictly increasing subsequence are
nonemptily isomorphic.  This compatibility orientation is from the subsequence object to the
full-diagram object. -/
theorem nonemptyIsoOfSubsequence (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    {Xsub Xfull : D}
    (hsub : HomotopyColimit.IsOf (SequentialDiagram.subsequence K hs) Xsub)
    (hfull : HomotopyColimit.IsOf K Xfull) : Nonempty (Xsub ≅ Xfull) := sorry

/-- Lemma 13.33.4: passing to a strictly increasing subsequence does not change whether a fixed
object is a homotopy colimit. -/
@[stacks 0CRJ]
theorem subsequence_iff (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s) {X : D} :
    HomotopyColimit.IsOf (SequentialDiagram.subsequence K hs) X ↔
      HomotopyColimit.IsOf K X := sorry

end IsOf

end HomotopyColimit

end CategoryTheory
