/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.Homology

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {G : X.Modules}

/-- Ext⁰ class of a map `Ω[f] ⟶ G`. -/
def homToExtZero (α : Ω[f] ⟶ G) : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj NL[f],
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
    (DerivedCategory.Q.map
      (augmentation f ≫
        (CochainComplex.singleFunctor (Modules X) 0).map α))

/-- `homToExtZero f` is `Q.map` of the augmentation followed by the degree-zero single of `α`. -/
theorem homToExtZero_apply (α : Ω[f] ⟶ G) :
    homToExtZero f α =
      (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
        (DerivedCategory.Q.map
          (augmentation f ≫
            (CochainComplex.singleFunctor (Modules X) 0).map α)) := sorry

/-- The identification `Hom(Ω[f], G) ≃ Ext⁰(Q NL[f], Q((G)[0]))`. -/
theorem homToExtZero_bijective :
    Function.Bijective (fun α : Ω[f] ⟶ G ↦ homToExtZero f α) := sorry

/-- Inverse of `homToExtZero f`: unshift the Ext⁰ class, pass to `H⁰`, and
identify `H⁰((G)[0])` with `G`. -/
def extZeroToHom (ξ : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj NL[f],
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) : Ω[f] ⟶ G :=
  homologyZeroInv f ≫
    (DerivedCategory.homologyFunctorFactors (Modules X) (0 : ℤ)).inv.app NL[f] ≫
    (DerivedCategory.homologyFunctor (Modules X) (0 : ℤ)).map
      ((CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules X) (0 : ℤ)).hom.app
      G

/-- `extZeroToHom f` inverts `homToExtZero f`. -/
theorem extZeroToHom_left_inv (α : Ω[f] ⟶ G) :
    extZeroToHom f (homToExtZero f α) = α := sorry

/-- `homToExtZero f` inverts `extZeroToHom f`. -/
theorem extZeroToHom_right_inv (ξ : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj NL[f],
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    homToExtZero f (extZeroToHom f ξ) = ξ := sorry

/-- Zero Ext⁰ corresponds to the zero map `Ω[f] ⟶ G`. -/
theorem extZeroToHom_zero :
    extZeroToHom f (0 : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj NL[f],
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) = 0 := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
