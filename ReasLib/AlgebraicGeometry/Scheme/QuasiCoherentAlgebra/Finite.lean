/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FinitePresentation
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Finite quasi-coherent algebra sheaves

This file defines finiteness of a quasi-coherent algebra sheaf through its underlying module and
states its approximation by finite, finitely presentable quasi-coherent algebra sheaves.
-/

@[expose] public section

open CategoryTheory Limits
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.Scheme.QcAlgebraUnder

/-- An algebra sheaf is finite when its underlying module over the structure sheaf is of finite
type. -/
abbrev finiteProperty (S : Scheme.{u}) :
    ObjectProperty (Under (schemeCommRingSheaf S)) :=
  fun A ↦
    ((restrictionAlong A.hom).obj
      (unitModule (Opens.grothendieckTopology S)
        (A.right : CategoryTheory.Sheaf
          (Opens.grothendieckTopology S) CommRingCat.{u}))).IsFiniteType

/-- A quasi-coherent algebra sheaf is finite exactly when its underlying module is of finite
type. -/
@[simp] theorem finiteProperty_iff (S : Scheme.{u}) (A : S.QcAlgebraUnder) :
    finiteProperty S A.obj ↔ (underlyingModule S A).IsFiniteType := Iff.rfl

/-- A finite quasi-coherent algebra sheaf on a quasi-compact quasi-separated scheme admits a
filtered colimit presentation by finite, quasi-coherent, finitely presentable algebra sheaves
whose transition morphisms are locally surjective on the underlying sheaves. -/
theorem exists_finite_finitelyPresentable_colimitPresentation_locallySurjective
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (A : S.QcAlgebraUnder) (hA : finiteProperty S A.obj) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I A.obj,
        (∀ i : I, finiteProperty S (pres.diag.obj i)) ∧
          (∀ i : I, finitelyPresentableProperty S (pres.diag.obj i)) ∧
            ∀ {i i' : I} (f : i ⟶ i'),
              CategoryTheory.Sheaf.IsLocallySurjective (pres.diag.map f).right := sorry

end AlgebraicGeometry.Scheme.QcAlgebraUnder

end
