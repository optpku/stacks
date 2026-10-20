module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Preservation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor

/-!
# Limit preservation for base-change properties of module morphisms

The subterminal functors detecting surjectivity, vanishing, and invertibility
of base-changed quasi-coherent module morphisms preserve directed affine limits
under finiteness and quasi-compact scheme-theoretic support hypotheses.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- If the target module is of finite type and its scheme-theoretic support
is quasi-compact over the base, a subterminal functor detecting epimorphic
base changes preserves directed affine limits. -/
theorem surjectivityFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [𝒢.IsFiniteType]
    [QuasiCompact ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (F_surj : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_surj.obj (op T))]
    (hF_surj : ∀ T : SchemeOver B,
      Nonempty (F_surj.obj (op T)) ↔ Epi (baseChangeMap f T.hom u)) :
    SchemeOver.PreservesDirectedAffineLimits B F_surj := sorry

/-- If the source module is of finite type and its scheme-theoretic support
is quasi-compact over the base, a subterminal functor detecting vanishing
base changes preserves directed affine limits. -/
theorem zeroFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType]
    [QuasiCompact ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (F_zero : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_zero.obj (op T))]
    (hF_zero : ∀ T : SchemeOver B,
      Nonempty (F_zero.obj (op T)) ↔ baseChangeMap f T.hom u = 0) :
    SchemeOver.PreservesDirectedAffineLimits B F_zero := sorry

/-- If the source module is of finite type, the target module is of finite
presentation, and both scheme-theoretic supports are quasi-compact over the
base, the isomorphism functor preserves directed affine limits. -/
theorem isomorphismFunctor_preservesDirectedAffineLimits
    (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsFinitePresentation]
    [QuasiCompact ((schemeTheoreticSupport ℱ).ι ≫ f)]
    [QuasiCompact ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    SchemeOver.PreservesDirectedAffineLimits B (isomorphismFunctor f u) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
