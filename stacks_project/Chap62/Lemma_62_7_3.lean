module

import StacksCheckRecall

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Equidimensional
public import stacks_project.Chap62.Lemma_62_8_2_Operations

/-!
# Functoriality of equidimensional relative cycles

Restriction, base change, and flat pullback preserve equidimensionality of
relative `r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open CyclesOnFibers

noncomputable section

universe u

namespace AlgebraicGeometry

open RelativeCycle

/- Lemma 62.7.3 (1): if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is an equidimensional relative `r`-cycle on `X / S`, then
any restriction of `α` to compatible opens `U ⊆ X` and `V ⊆ S` is
equidimensional. -/
@[stacks 0H5K] #check (AlgebraicGeometry.equidimensional_restrict :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r},
    IsRelative α → Equidimensional α → (U : X.Opens) → (V : S.Opens) →
      (hUV : U ≤ f ⁻¹ᵁ V) →
        Equidimensional (FiberCycleFamily.restrict U V hUV α))

/- Lemma 62.7.3 (2): if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is an equidimensional relative `r`-cycle on `X / S`, then
any base change of `α` along `g : S' ⟶ S` is equidimensional. -/
@[stacks 0H5K] #check (AlgebraicGeometry.equidimensional_baseChange :
  ∀ {X S S' : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (g : S' ⟶ S) {r : ℕ}
    {α : Family f r}, IsRelative α → Equidimensional α →
      Equidimensional (baseChange f g r α))

/- Lemma 62.7.3 (3): if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is an equidimensional relative `r`-cycle on `X / S`, then
any flat pullback of `α` along a flat morphism of relative dimension `e` is
equidimensional. -/
@[stacks 0H5K] #check (AlgebraicGeometry.equidimensional_flatPullback :
  ∀ {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (h : X' ⟶ X) (e : ℕ)
    [Flat h] [RelativeDimension h e] {r : ℕ} {α : Family f r},
    IsRelative α → Equidimensional α →
      Equidimensional (RelativeCycle.flatPullback h e α))

end AlgebraicGeometry
