/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

/- Theorem 59.17.4 (Meta theorem on quasi-coherent sheaves) (1) -/
@[stacks 03OJ]
#check (AlgebraicGeometry.Scheme.AssociatedModule.structurePresheaf_isSheaf_of_fpqc :
  ∀ (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : Precoverage C) (p : C ⥤ Over S)
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [J.PullbacksPreservedBy (p ⋙ Over.forget S)]
    (h_fpqc : J ≤ Scheme.fpqcPrecoverage.comap (p ⋙ Over.forget S)),
    Presheaf.IsSheaf J.toGrothendieck (Scheme.Over.structurePresheaf p))

/- Theorem 59.17.4 (Meta theorem on quasi-coherent sheaves) (2) -/
@[stacks 03OJ]
#check (AlgebraicGeometry.Scheme.AssociatedModule.exists_iso :
  ∀ (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : Precoverage C) (p : C ⥤ Over S)
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [J.PullbacksPreservedBy (p ⋙ Over.forget S)]
    [p.Full] [p.Faithful]
    [p.IsCocontinuous J.toGrothendieck (Scheme.zariskiTopology.over S)]
    (h_fpqc : J ≤ Scheme.fpqcPrecoverage.comap (p ⋙ Over.forget S))
    (h_terminal : ∃ X : C, p.obj X = Over.mk (𝟙 S))
    [∀ X : C, HasWeakSheafify (J.toGrothendieck.over X) AddCommGrpCat]
    [∀ X : C, (J.toGrothendieck.over X).WEqualsLocallyBijective AddCommGrpCat],
    ∀ (M : SheafOfModules.{u}
      ⟨Scheme.Over.structurePresheaf p,
        AlgebraicGeometry.Scheme.AssociatedModule.structurePresheaf_isSheaf_of_fpqc
          S J p h_fpqc⟩),
      M.IsQuasicoherent →
        ∃ F : Scheme.QCoh S,
          Nonempty
            (Scheme.Modules.pullbackSectionsPresheaf p F.obj ≅ M.val))
