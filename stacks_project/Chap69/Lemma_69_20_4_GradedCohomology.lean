/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Graded.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Graded

/-! # Graded cohomology of modules on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde
open AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology
open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check (AlgebraicGeometry.AlgebraicSpace.Modules.GradedModule.IsFiniteType :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {𝓑 : ℤ → X.Modules}
    {alg : OXGradedAlgebra 𝓑}, GradedModule alg → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology.cohomologyOver :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules], X.Modules → ℕ → ModuleCat A)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology.carrier :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules} {alg : OXGradedAlgebra 𝓑},
    GradedModule alg → ℕ → Type u)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology.module :
  ∀ {S : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] {𝓑 : ℤ → X.Modules}
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra)
    (p : ℕ), Module B (carrier σA f F p))
