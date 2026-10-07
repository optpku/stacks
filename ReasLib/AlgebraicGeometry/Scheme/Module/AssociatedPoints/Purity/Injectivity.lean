module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FiberSpecialization
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Injectivity
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.TensorPullback

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsPureAlong

/-- For a finite-type quasicoherent module that is pure along the closed fibre and flat over
an affine local base, a module morphism is monic exactly when its stalk maps are injective at
the associated points of that fibre. -/
theorem mono_iff_stalk_injective_on_fiber_associatedPoints
    {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent]
    [ℱ.IsFiniteType] [𝒢.IsQuasicoherent] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (h_pure : ℱ.IsPureAlong f s) (h_flat : flatOver ℱ f) (φ : ℱ ⟶ 𝒢) :
    (∀ x : f.fiber s,
      x ∈ ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints →
        Function.Injective (RingedSpace.moduleStalkHom (f.fiberι s x) φ)) ↔
      Mono φ := sorry

end AlgebraicGeometry.Scheme.Modules.IsPureAlong
