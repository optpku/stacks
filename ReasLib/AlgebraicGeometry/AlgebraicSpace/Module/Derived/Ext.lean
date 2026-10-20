/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Linearity

/-!
# Derived Ext modules over an affine base

The chartwise action of the affine base induces the module-valued shifted-Hom bifunctor
on the derived category of module sheaves of an algebraic space.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The shifted-Hom bifunctor with its `A`-module structure induced by a morphism
`f : X ⟶ ofOver (Over.mk (𝟙 (Spec A)))`. -/
noncomputable def bifunctor
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (n : ℤ) :
    (ModuleDerived X)ᵒᵖ ⥤ ModuleDerived X ⥤ ModuleCat.{u + 1} A :=
  @CategoryTheory.ShiftedHom.linearCoyoneda A _
    (ModuleDerived X) _ _
    (@DerivedCategory.instLinear A _ (Modules X) _ _
      (Modules.baseLinear f) _)
    _ n

/-- The `A`-module of degree-`n` derived extensions from `K` to `L`, with scalar action
induced by `f`. -/
noncomputable abbrev value
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (K L : ModuleDerived X) (n : ℤ) : ModuleCat.{u + 1} A :=
  ((bifunctor f n).obj (op K)).obj L

/-- Forgetting the `A`-action on `value f K L n` recovers the shifted-morphism group
`Ext⁽n⁾(K, L)`. -/
theorem value_forget
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (K L : ModuleDerived X) (n : ℤ) :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (value f K L n) =
      AddCommGrpCat.of (Ext⁽n⁾(K, L)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt
