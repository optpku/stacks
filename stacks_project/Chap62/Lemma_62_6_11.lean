module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.LocallyConstant.Basic
public import stacks_project.Chap62.Lemma_62_6_11_RelativeCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.11: if `S` is locally Noetherian and `f : X ⟶ S` is smooth of
relative dimension `r ≥ 0`, then for every relative `r`-cycle `α` the support of
`α` is clopen in `X`. A sharper fact used in the proof is that the
fibre-component coefficient function `x ↦ n_x` is locally constant. -/
@[stacks 0H5B]
theorem isClopen_support {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : Family f r) (hα : IsRelative α) :
    IsClopen (support α) := sorry

/-- The coefficient of a fibrewise `r`-cycle at those generic points of the fibre
`X_s` which specialize to `x`, where `s` is the image of `x`. Under smoothness of
relative dimension `r` this is the coefficient `n_x` of the unique irreducible
component of `X_s` through `x`. -/
noncomputable def componentCoeff {X S : Scheme.{u}} (f : X ⟶ S) {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : Family f r) (x : X) : ℤ :=
  ∑ᶠ ξ : f.fiber (f x),
    @ite ℤ (f.asFiber x ∈ closure {ξ}) (Classical.propDecidable _)
      (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (f x)) r (α (f x)) ξ) 0

/-- The fibre-component coefficient is the finite sum of coefficients of generic
points of the fibre specializing to the given point. -/
theorem componentCoeff_apply {X S : Scheme.{u}} (f : X ⟶ S) {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : Family f r) (x : X) :
    componentCoeff f α x =
      ∑ᶠ ξ : f.fiber (f x),
        @ite ℤ (f.asFiber x ∈ closure {ξ}) (Classical.propDecidable _)
          (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (f x)) r (α (f x)) ξ) 0 :=
  sorry

/-- If `α` is a relative `r`-cycle on a smooth morphism of relative dimension `r`
to a locally Noetherian base, then the fibre-component coefficient function is
locally constant. -/
theorem isLocallyConstant_componentCoeff {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : Family f r) (hα : IsRelative α) :
    IsLocallyConstant (componentCoeff f α) := sorry

/-- Under smoothness of relative dimension `r`, the support of a relative
`r`-cycle is the function support of its fibre-component coefficient. -/
theorem support_eq_componentCoeff_support {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : Family f r) (hα : IsRelative α) :
    support α = Function.support (componentCoeff f α) := sorry

end AlgebraicGeometry.RelativeCycle
