module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.11: if `S` is locally Noetherian and `f : X ⟶ S` is smooth of
relative dimension `r ≥ 0`, then for every relative `r`-cycle `α` the support of
`α` is clopen in `X`. A sharper fact used in the proof is that the
fibre-component coefficient function `x ↦ n_x` is locally constant. -/
@[stacks 0H5B] #check (AlgebraicGeometry.RelativeCycle.isClopen_support :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r : ℕ} [SmoothOfRelativeDimension r f] (α : CyclesOnFibers f r),
    IsRelative α → IsClopen (CyclesOnFibers.support α))

/- The coefficient of a fibrewise `r`-cycle at those generic points of the fibre
`X_s` which specialize to `x`, where `s` is the image of `x`. Under smoothness of
relative dimension `r` this is the coefficient `n_x` of the unique irreducible
component of `X_s` through `x`. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.componentCoeff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) {r : ℤ}, CyclesOnFibers f r → X → ℤ)

/- The fibre-component coefficient is the finite sum of coefficients of generic
points of the fibre specializing to the given point. -/
open scoped Classical in
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.componentCoeff_apply :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) {r : ℤ} (α : CyclesOnFibers f r) (x : X),
    CyclesOnFibers.componentCoeff f α x =
      ∑ᶠ ξ : f.fiber (f x),
        if f.asFiber x ∈ closure {ξ} then (α.toAlgebraicCycle (f x)) ξ else 0)

/- If `α` is a relative `r`-cycle on a smooth morphism of relative dimension `r`
to a locally Noetherian base, then the fibre-component coefficient function is
locally constant. -/
#check (AlgebraicGeometry.RelativeCycle.isLocallyConstant_componentCoeff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r : ℕ} [SmoothOfRelativeDimension r f] (α : CyclesOnFibers f r),
    IsRelative α → IsLocallyConstant (CyclesOnFibers.componentCoeff f α))

/- Under smoothness of relative dimension `r`, the support of a relative
`r`-cycle is the function support of its fibre-component coefficient. -/
#check (AlgebraicGeometry.RelativeCycle.support_eq_componentCoeff_support :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    {r : ℕ} [SmoothOfRelativeDimension r f] (α : CyclesOnFibers f r),
    IsRelative α →
      CyclesOnFibers.support α = Function.support (CyclesOnFibers.componentCoeff f α))

end AlgebraicGeometry.RelativeCycle
