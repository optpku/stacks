/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- On an affine scheme, a finitely presented quasi-coherent module admits a nonzero morphism to
every nonzero quasi-coherent module whose support is contained in its support. -/
@[stacks 0GPF]
theorem exists_nonzero_hom_of_moduleSupport_subset
    {X : Scheme.{u}} [IsAffine X] (F E : Scheme.QCoh X)
    [F.obj.IsFinitePresentation] (hE : ¬ IsZero E)
    (h_support : Scheme.Modules.moduleSupport E.obj ⊆
      Scheme.Modules.moduleSupport F.obj) :
    ∃ f : F ⟶ E, f ≠ 0 := sorry

/-- For a finitely presented quasi-coherent module on a quasi-compact and quasi-separated scheme,
the modules supported on it are the smallest Serre object property containing it and closed under
arbitrary direct sums. -/
theorem support_eq_serreCoproductClosure
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Scheme.QCoh X) [F.obj.IsFinitePresentation] :
    (fun E : Scheme.QCoh X ↦
      Scheme.Modules.moduleSupport E.obj ⊆ Scheme.Modules.moduleSupport F.obj) =
      sInf {P : ObjectProperty (Scheme.QCoh X) |
        P F ∧ P.IsSerreClass ∧
          ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)} := sorry

end AlgebraicGeometry.Scheme.QCoh
