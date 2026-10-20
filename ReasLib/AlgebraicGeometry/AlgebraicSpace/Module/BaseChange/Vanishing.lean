module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Vanishing of a fibre pullback at a closure point

A morphism of quasi-coherent modules on a locally finitely presented algebraic space
over an affine scheme, with finitely presented target flat over the base, vanishes on
the fibre over every closure point of a subset on whose fibres it vanishes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Let `X` be a locally finitely presented algebraic space over an affine scheme `S`,
and let `u : ℱ ⟶ 𝒢` be a morphism of quasi-coherent modules with `𝒢` finitely presented
and flat over `S`. If the pullback of `u` to the scheme-theoretic fibre at every point
of `T ⊆ S` vanishes, then its pullback to the fibre at every point of `closure T`
vanishes. -/
@[stacks 0CWB]
theorem baseChangeMap_eq_zero_of_mem_closure
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S}
    [LocallyOfFinitePresentation (SchemeRealization.toBase X)] {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsFinitePresentation]
    (hG_flat : flatOver 𝒢 (SchemeRealization.toBase X)) (u : ℱ ⟶ 𝒢) (T : Set S) {s : S}
    (hs : s ∈ closure T)
    (hT : ∀ t ∈ T, baseChangeMap (SchemeRealization.toBase X) (residueFieldHom S t) u = 0) :
    baseChangeMap (SchemeRealization.toBase X) (residueFieldHom S s) u = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
