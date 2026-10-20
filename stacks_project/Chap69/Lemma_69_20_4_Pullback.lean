/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Graded.Pullback

/-! # Pullbacks of affine tilde graded algebras on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde
open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.sectionsPullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules),
    F.sections → ((pullback f).obj F).sections)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde.affineTildeSection :
  ∀ {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) (n : ℕ), 𝒜 n →
    (modulesSpecToSheaf.obj (tilde (ModuleCat.of (CommRingCat.of A) (𝒜 n)))).presheaf.obj
      (Opposite.op ⊤))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde.OXGradedAlgebra.oneSection :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules},
    OXGradedAlgebra 𝓑 → (𝓑 0).sections)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde.Comparison.toPullbackIso :
  ∀ {S : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    {σA : Spec (CommRingCat.of A) ⟶ S} {f : X ⟶ ofOver (Over.mk σA)}
    {𝓑 : ℤ → X.Modules} (pullbackData : Comparison 𝒜 σA f 𝓑),
    ∀ n : ℕ, (pullback f).obj (pullbackData.tildeB n) ≅ 𝓑 n)
