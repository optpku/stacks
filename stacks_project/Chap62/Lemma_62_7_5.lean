module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional.FppfDescent

/-!
# Fppf descent of equidimensional relative cycles

Equidimensionality of a relative `r`-cycle on `X / S` may be checked after
base change along an fppf covering of `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.7.5: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` locally
Noetherian and `f` locally of finite type. Let `r ≥ 0` be an integer. Let `α`
be a relative `r`-cycle on `X / S`. Let `{g i : Si i ⟶ S}` be an fppf covering.
Then `α` is equidimensional if and only if each base change
`baseChange f (g i) r α` is equidimensional. -/
@[stacks 0H5M] #check (AlgebraicGeometry.RelativeCycle.isEquidimensional_iff_of_fppfCover :
  ∀ {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) (𝒰 : FppfCover.{u, v} S),
    Equidimensional α ↔
      ∀ i : 𝒰.I₀, Equidimensional (FamilyOfCyclesOnFibres.baseChange f (𝒰.f i) r α))

/- Equidimensionality of a relative `r`-cycle may be checked after base change
along an indexed fppf covering family `{g i : Si i ⟶ S}`. -/
#check (AlgebraicGeometry.RelativeCycle.isEquidimensional_iff_of_fppfCovering :
  ∀ {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α)
    {ι : Type v} {Si : ι → Scheme.{u}} (g : (i : ι) → Si i ⟶ S)
    (hg : Scheme.FppfCovering (fun i ↦ Over.mk (g i))),
    Equidimensional α ↔
      ∀ i, Equidimensional (FamilyOfCyclesOnFibres.baseChange f (g i) r α))

end AlgebraicGeometry.RelativeCycle
