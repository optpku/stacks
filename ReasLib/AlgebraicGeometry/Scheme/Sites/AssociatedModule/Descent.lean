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

/-- Under a fully faithful realization into schemes over `S` that refines Zariski
covers and preserves fpqc covers, the global-functions presheaf is a sheaf. -/
theorem structurePresheaf_isSheaf_of_fpqc
    (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (p : C ⥤ Over S)
    [p.Full] [p.Faithful]
    [p.IsCocontinuous J (Scheme.zariskiTopology.over S)]
    (h_fpqc : CoverPreserving J Scheme.fpqcTopology (p ⋙ Over.forget S))
    (h_terminal : ∃ X : C, p.obj X = Over.mk (𝟙 S)) :
    Presheaf.IsSheaf J (Scheme.Over.structurePresheaf p) := sorry

/-- Every quasi-coherent module sheaf for the induced structure sheaf is the
pullback-sections presheaf of a quasi-coherent module on `S`. -/
theorem exists_iso
    (S : Scheme.{u}) {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (p : C ⥤ Over S)
    [p.Full] [p.Faithful]
    [p.IsCocontinuous J (Scheme.zariskiTopology.over S)]
    (h_fpqc : CoverPreserving J Scheme.fpqcTopology (p ⋙ Over.forget S))
    (h_terminal : ∃ X : C, p.obj X = Over.mk (𝟙 S))
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat] :
    ∀ (M : SheafOfModules.{u}
      ⟨Scheme.Over.structurePresheaf p,
        structurePresheaf_isSheaf_of_fpqc S J p h_fpqc h_terminal⟩),
      M.IsQuasicoherent →
        ∃ F : Scheme.QCoh S,
          Nonempty
            (Scheme.Modules.pullbackSectionsPresheaf p F.obj ≅ M.val) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
