/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
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

/-- Lemma 62.7.3 (1): if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is an equidimensional relative `r`-cycle on `X / S`, then
any restriction of `α` to compatible opens `U ⊆ X` and `V ⊆ S` is
equidimensional. -/
@[stacks 0H5K]
theorem equidimensional_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (h_rel : IsRelative α) (h_eq : Equidimensional α) (U : X.Opens) (V : S.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    Equidimensional (FiberCycleFamily.restrict U V hUV α) := sorry

/-- Lemma 62.7.3 (2): if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is an equidimensional relative `r`-cycle on `X / S`, then
any base change of `α` along `g : S' ⟶ S` is equidimensional. -/
@[stacks 0H5K]
theorem equidimensional_baseChange {X S S' : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (g : S' ⟶ S) {r : ℕ}
    {α : Family f r} (h_rel : IsRelative α) (h_eq : Equidimensional α) :
    Equidimensional (baseChange f g r α) := sorry

/-- Lemma 62.7.3 (3): if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is an equidimensional relative `r`-cycle on `X / S`, then
any flat pullback of `α` along a flat morphism of relative dimension `e` is
equidimensional. -/
@[stacks 0H5K]
theorem equidimensional_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (h : X' ⟶ X) (e : ℕ)
    [Flat h] [RelativeDimension h e] {r : ℕ} {α : Family f r}
    (h_rel : IsRelative α) (h_eq : Equidimensional α) :
    Equidimensional (flatPullback h e α) := sorry

end AlgebraicGeometry
