/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Geometric covering families induce a continuous realization into the fpqc site.
Only pairwise pullbacks of members of a selected cover need to be preserved.
In particular, preservation of covering sieves alone is insufficient. -/
theorem isContinuous_of_fpqc_precoverage
    (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : Precoverage C) (p : C ⥤ Over S)
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [J.PullbacksPreservedBy (p ⋙ Over.forget S)]
    (h_fpqc : J ≤ Scheme.fpqcPrecoverage.comap (p ⋙ Over.forget S)) :
    (p ⋙ Over.forget S).IsContinuous J.toGrothendieck Scheme.fpqcTopology :=
  Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy _ _ _ h_fpqc

/-- The global-functions presheaf is a sheaf for a site presented by fpqc
covering families whose pairwise pullbacks are preserved in schemes.

The presentation records the covering-pullback existence in Stacks 00VH(3),
while `PullbacksPreservedBy` records that the overlaps used are the geometric
ones. For a geometric site as in Stacks 03OJ, use its covering families
and their scheme pullbacks; preservation of these pullbacks is explicit,
not inferred from fullness. Fullness, Zariski refinement, and a terminal
object are only needed for module descent. -/
theorem structurePresheaf_isSheaf_of_fpqc
    (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : Precoverage C) (p : C ⥤ Over S)
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [J.PullbacksPreservedBy (p ⋙ Over.forget S)]
    (h_fpqc : J ≤ Scheme.fpqcPrecoverage.comap (p ⋙ Over.forget S)) :
    Presheaf.IsSheaf J.toGrothendieck (Scheme.Over.structurePresheaf p) := sorry

/-- Every quasi-coherent module sheaf for the induced structure sheaf is the
pullback-sections presheaf of a quasi-coherent module on `S`.

As in `structurePresheaf_isSheaf_of_fpqc`, the selected covering families must
have geometric overlaps; arbitrary covering-sieve preservation does not suffice. -/
theorem exists_iso
    (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : Precoverage C) (p : C ⥤ Over S)
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [J.PullbacksPreservedBy (p ⋙ Over.forget S)]
    [p.Full] [p.Faithful]
    [p.IsCocontinuous J.toGrothendieck (Scheme.zariskiTopology.over S)]
    (h_fpqc : J ≤ Scheme.fpqcPrecoverage.comap (p ⋙ Over.forget S))
    (h_terminal : ∃ X : C, p.obj X = Over.mk (𝟙 S))
    [∀ X : C, HasWeakSheafify (J.toGrothendieck.over X) AddCommGrpCat]
    [∀ X : C, (J.toGrothendieck.over X).WEqualsLocallyBijective AddCommGrpCat] :
    ∀ (M : SheafOfModules.{u}
      ⟨Scheme.Over.structurePresheaf p,
        structurePresheaf_isSheaf_of_fpqc S J p h_fpqc⟩),
      M.IsQuasicoherent →
        ∃ F : Scheme.QCoh S,
          Nonempty
            (Scheme.Modules.pullbackSectionsPresheaf p F.obj ≅ M.val) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
