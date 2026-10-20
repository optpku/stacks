/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor

/-!
# Limit preservation for base-change properties of module morphisms

This module records preservation of directed affine limits by functors
detecting properties of base-changed morphisms of quasicoherent scheme modules.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- If the structural morphism is quasi-compact and the target module is of
finite type, a subterminal functor detecting epimorphic base changes preserves
directed affine limits. -/
theorem surjectivityFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [QuasiCompact f] [𝒢.IsFiniteType]
    (F_surj : (Over S)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : Over S, Subsingleton (F_surj.obj (op T))]
    (hF_surj : ∀ T : Over S,
      Nonempty (F_surj.obj (op T)) ↔ Epi (baseChangeMap f T.hom u)) :
    Scheme.Over.PreservesDirectedAffineLimits S F_surj := sorry

/-- If the structural morphism is quasi-compact and the source module is of
finite type, a subterminal functor detecting zero base changes preserves
directed affine limits. -/
theorem zeroFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [QuasiCompact f] [ℱ.IsFiniteType]
    (F_zero : (Over S)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : Over S, Subsingleton (F_zero.obj (op T))]
    (hF_zero : ∀ T : Over S,
      Nonempty (F_zero.obj (op T)) ↔ baseChangeMap f T.hom u = 0) :
    Scheme.Over.PreservesDirectedAffineLimits S F_zero := sorry

/-- If the structural morphism is quasi-compact, the source module is of
finite type, and the target module is of finite presentation, the functor
detecting isomorphic base changes preserves directed affine limits. -/
theorem isomorphismFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [QuasiCompact f] [ℱ.IsFiniteType] [𝒢.IsFinitePresentation] :
    Scheme.Over.PreservesDirectedAffineLimits S (isomorphismFunctor f u) := sorry

end AlgebraicGeometry.Scheme.Modules
