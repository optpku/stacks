/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Descent
import StacksCheckRecall

/-!
# Detection of quasi-coherence on a covering of algebraic stacks

On an algebraic stack, quasi-coherence of an étale module is detected on a
jointly point-covering family of smooth morphisms, and quasi-coherence of an
fppf module is detected on a jointly point-covering family of flat and locally
finitely presented morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u v

/- Lemma 103.16.1 (1): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a
family of smooth morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_étale`. If
each inverse image `(etaleModuleInverseImage (f j)).obj F` is quasi-coherent, then so
is `F`. -/
@[stacks 07AZ]
#check (AlgebraicGeometry.AlgebraicStack.isQuasicoherent_of_smoothCovering :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_qc : ∀ j, ((etaleModuleInverseImage (f j)).obj F).IsQuasicoherent),
    F.IsQuasicoherent)

/- Lemma 103.16.1 (2): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a
family of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_fppf`. If
each inverse image `(modulePullback (f j)).obj F` is quasi-coherent, then so
is `F`. -/
@[stacks 07AZ]
#check (AlgebraicGeometry.AlgebraicStack.isQuasicoherent_of_fppfCovering :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)]
    [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_qc : ∀ j, ((modulePullback (f j)).obj F).IsQuasicoherent),
    F.IsQuasicoherent)
