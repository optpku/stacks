/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every quasi-coherent module on a quasi-compact quasi-separated scheme is a filtered colimit
of finitely presented modules. -/
theorem isFinitePresentation_ind
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ind.{u} F := sorry

/-- A finite-type quasi-coherent module on a quasi-compact quasi-separated scheme admits a
filtered colimit presentation by finitely presented modules with epimorphic transition maps. -/
theorem exists_finitePresentation_colimitPresentation_epi
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I F,
        (∀ i : I, (pres.diag.obj i).IsFinitePresentation) ∧
          ∀ {i i' : I} (f : i ⟶ i'), Epi (pres.diag.map f) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.QCoh

/-- A quasi-coherent module on a quasi-compact quasi-separated scheme is finitely presentable
if and only if its underlying module sheaf is of finite presentation. -/
theorem isFinitelyPresentable_iff_isFinitePresentation
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Scheme.QCoh X) :
    CategoryTheory.IsFinitelyPresentable.{u} F ↔ F.obj.IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.QCoh

end
