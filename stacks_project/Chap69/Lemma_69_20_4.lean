/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap69.Lemma_69_20_4_GradedCohomology

/-!
# Lemma 69.20.4

Cohomology of a quasi-coherent finite-type graded module over the pullback of an affine
tilde algebra, for a proper algebraic space over a Noetherian affine base, is a finite
module over the graded algebra.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace GradedCohomology

/-- Lemma 69.20.4: if `A` is a Noetherian ring, `B` is a finitely generated graded `A`-algebra,
`f : X ⟶ ofOver (Over.mk σA)` is a proper morphism of algebraic spaces to `Spec(A)` over a
scheme `S`, `𝓑` is identified with `f^*(tilde B)` by a pullback-tilde comparison, and `F` is a
quasi-coherent graded `𝓑`-module of finite type, then for every `p : ℕ` the graded `B`-module
`carrier σA f F p` is a finite `B`-module under the canonical action `module`. Here
`ofOver (Over.mk σA)` is `Spec(A)` as an algebraic space over `S`, and `carrier` is the
graded `B`-module `H^p(X, F)`. -/
@[stacks 08AT]
theorem finite {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : AlgebraicSpace S} (σA : Spec (CommRingCat.of A) ⟶ S)
    (f : X ⟶ ofOver (Over.mk σA)) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (𝓑 : ℤ → X.Modules)
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra)
    (hFQuasicoherent : ∀ n : ℤ, (F.obj n).IsQuasicoherent)
    (hFFiniteType : F.IsFiniteType) (p : ℕ) :
    Module.FiniteWithAction B (carrier σA f F p) (module 𝒜 σA f pullbackData F p) :=
  sorry

end GradedCohomology

end AlgebraicGeometry.AlgebraicSpace.Modules
