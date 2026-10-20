/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Finite.Explicit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Graded
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open PullbackTilde

/- Lemma 30.19.3 (1): let `A` be a Noetherian ring, `B` a finitely generated nonnegatively
graded `A`-algebra, and `f : X ⟶ Spec(A)` a proper morphism. Set `𝓑` to the pullback along `f` of the associated sheaf of `B`. If
`ℱ` is a quasicoherent finite-type graded `𝓑`-module, then for every `p ≥ 0` the graded
cohomology `H^p(X, ℱ)` is finite over the canonical `B`-action induced by this pullback. -/
@[stacks 0897 "(1)"]
#check
  (GradedCohomology.finite :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
      (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (𝓑 : GradedAlgebraSheaf.{u, u} X.sheaf)
      (h𝓑 : Comparison 𝒜 f 𝓑)
      (ℱ : GradedModuleSheaf.{u, u} 𝓑)
      (hℱQuasicoherent : ∀ n : ℤ, (ℱ n).IsQuasicoherent)
      (hℱFiniteType : GradedModuleSheaf.IsFiniteType.{u, u} (𝒜 := 𝓑) ℱ)
      (p : ℕ),
      Module.FiniteWithAction B (GradedCohomology.carrier ℱ p)
        (GradedCohomology.module 𝒜 f h𝓑 ℱ p))

/- Lemma 30.19.3 (2): under the same hypotheses, if `𝓛` is an ample invertible `𝒪_X`-module,
then there exists an integer `d₀` such that `H^p(X, ℱ ⊗ 𝓛^⊗ d) = 0` for all `p > 0` and all
`d ≥ d₀`. -/
@[stacks 0897 "(2)"]
#check
  (GradedCohomology.twist_eventually_isZero :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
      (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (𝓑 : GradedAlgebraSheaf.{u, u} X.sheaf)
      (h𝓑 : Comparison 𝒜 f 𝓑)
      (ℱ : GradedModuleSheaf.{u, u} 𝓑)
      (hℱQuasicoherent : ∀ n : ℤ, (ℱ n).IsQuasicoherent)
      (hℱFiniteType : GradedModuleSheaf.IsFiniteType.{u, u} (𝒜 := 𝓑) ℱ)
      [MonoidalCategory X.Modules] (L : X.Modules) [Invertible L] [IsAmple L],
      ∃ d0 : ℤ, ∀ d : ℤ, d0 ≤ d → ∀ p : ℕ, 0 < p →
        IsZero (AddCommGrpCat.of (GradedCohomology.twist L ℱ d p)))

end AlgebraicGeometry.Scheme.Modules
