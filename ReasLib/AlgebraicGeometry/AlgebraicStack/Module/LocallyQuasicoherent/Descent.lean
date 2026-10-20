/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocallyQuasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback

/-!
# Detection of local quasi-coherence on an fppf covering of algebraic stacks

Local quasi-coherence of an fppf module is detected on a jointly point-covering
family of flat and locally finitely presented morphisms of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- An fppf module on an algebraic stack is locally quasi-coherent if its inverse
images along a jointly point-covering family of flat and locally finitely
presented morphisms of algebraic stacks are locally quasi-coherent. -/
@[stacks 07AP]
theorem isLocallyQuasicoherent_of_fppfCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_lqc : ∀ j, IsLocallyQuasicoherent ((modulePullback (f j)).obj F).val) :
    IsLocallyQuasicoherent F.val :=
  sorry

/-- If `f : Y ⟶ X` is a flat and locally finitely presented morphism of algebraic
stacks which is surjective on points, then an fppf `𝒪_X`-module is locally
quasi-coherent as soon as its inverse image along `f` is. -/
theorem isLocallyQuasicoherent_of_fppf_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_cover : Function.Surjective (Points.map f))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_lqc : IsLocallyQuasicoherent ((modulePullback f).obj F).val) :
    IsLocallyQuasicoherent F.val :=
  sorry

end AlgebraicGeometry.AlgebraicStack
