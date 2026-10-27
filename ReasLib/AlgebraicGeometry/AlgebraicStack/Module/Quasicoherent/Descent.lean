/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Quasi-coherent module descent along coverings of algebraic stacks

Quasi-coherence is detected along jointly point-covering smooth families for
étale modules and flat, locally finitely presented families for fppf modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- An étale module on an algebraic stack is quasi-coherent if its inverse
images along a jointly point-covering family of smooth morphisms of algebraic
stacks are quasi-coherent. -/
@[stacks 07AZ]
theorem isQuasicoherent_of_smoothCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_qc : ∀ j, ((etaleModuleInverseImage (f j)).obj F).IsQuasicoherent) :
    F.IsQuasicoherent := sorry

/-- An fppf module on an algebraic stack is quasi-coherent if its inverse
images along a jointly point-covering family of flat and locally finitely
presented morphisms of algebraic stacks are quasi-coherent. -/
@[stacks 07AZ]
theorem isQuasicoherent_of_fppfCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)]
    [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_qc : ∀ j, ((modulePullback (f j)).obj F).IsQuasicoherent) :
    F.IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicStack
