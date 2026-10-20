/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Limit
import StacksCheckRecall

/-!
# Lemma 77.7.4

In Situation 77.7.1, the subterminal flattening functors on schemes over `B`
preserve directed inverse limits of affine schemes under finite type / finite
presentation and quasi-compact scheme-theoretic support hypotheses.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 77.7.4 (1): Surjectivity is limit preserving under the stated
finiteness and quasi-compact scheme-theoretic support hypotheses. -/
@[stacks 083J] #check (AlgebraicGeometry.AlgebraicSpace.Modules.surjectivityFunctor_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (u : ℱ ⟶ 𝒢) [𝒢.IsFiniteType]
    [QuasiCompact ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (F_surj : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_surj.obj (op T))]
    (hF_surj : ∀ T : SchemeOver B,
      Nonempty (F_surj.obj (op T)) ↔ Epi (baseChangeMap f T.hom u)),
    SchemeOver.PreservesDirectedAffineLimits B F_surj)

/- Lemma 77.7.4 (2): Vanishing is limit preserving under the stated
finiteness and quasi-compact scheme-theoretic support hypotheses. -/
@[stacks 083J] #check (AlgebraicGeometry.AlgebraicSpace.Modules.zeroFunctor_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType]
    [QuasiCompact ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (F_zero : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_zero.obj (op T))]
    (hF_zero : ∀ T : SchemeOver B,
      Nonempty (F_zero.obj (op T)) ↔ baseChangeMap f T.hom u = 0),
    SchemeOver.PreservesDirectedAffineLimits B F_zero)

/- Lemma 77.7.4 (3): Isomorphism is limit preserving under the stated
finiteness and quasi-compact scheme-theoretic support hypotheses. -/
@[stacks 083J] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsFinitePresentation]
    [QuasiCompact ((schemeTheoreticSupport ℱ).ι ≫ f)]
    [QuasiCompact ((schemeTheoreticSupport 𝒢).ι ≫ f)],
    SchemeOver.PreservesDirectedAffineLimits B (isomorphismFunctor f u))
