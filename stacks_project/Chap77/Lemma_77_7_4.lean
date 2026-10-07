module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»
public import stacks_project.Chap77.Lemma_77_7_4_Limit

/-!
# Lemma 77.7.4

In Situation 77.7.1, the subterminal flattening functors on schemes over `B`
preserve directed inverse limits of affine schemes under finite type / finite
presentation and quasi-compact scheme-theoretic support hypotheses.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- Lemma 77.7.4 (1): In Situation 77.7.1, if `𝒢` is of finite type and the
scheme-theoretic support of `𝒢` is quasi-compact over `B`, then a subterminal
functor detecting epimorphicity of `baseChangeMap f T.hom u` preserves directed
affine limits on `SchemeOver B`. -/
@[stacks 083J]
theorem surjectivityFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [𝒢.IsFiniteType]
    [QuasiCompact ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (F_surj : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_surj.obj (op T))]
    (hF_surj : ∀ T : SchemeOver B,
      Nonempty (F_surj.obj (op T)) ↔ Epi (baseChangeMap f T.hom u)) :
    SchemeOver.PreservesDirectedAffineLimits B F_surj := sorry

/-- Lemma 77.7.4 (2): In Situation 77.7.1, if `ℱ` is of finite type and the
scheme-theoretic support of `ℱ` is quasi-compact over `B`, then a subterminal
functor detecting vanishing of `baseChangeMap f T.hom u` preserves directed
affine limits on `SchemeOver B`. -/
@[stacks 083J]
theorem zeroFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType]
    [QuasiCompact ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (F_zero : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_zero.obj (op T))]
    (hF_zero : ∀ T : SchemeOver B,
      Nonempty (F_zero.obj (op T)) ↔ baseChangeMap f T.hom u = 0) :
    SchemeOver.PreservesDirectedAffineLimits B F_zero := sorry

/-- Lemma 77.7.4 (3): In Situation 77.7.1, if `ℱ` is of finite type, `𝒢` is of
finite presentation, and the scheme-theoretic supports of `ℱ` and `𝒢` are
quasi-compact over `B`, then `isomorphismFunctor f u` preserves directed affine
limits on `SchemeOver B`. -/
@[stacks 083J]
theorem isomorphismFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsFinitePresentation]
    [QuasiCompact ((schemeTheoreticSupport ℱ).ι ≫ f)]
    [QuasiCompact ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    SchemeOver.PreservesDirectedAffineLimits B (isomorphismFunctor f u) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
