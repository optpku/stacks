/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import stacks_project.Chap62.Lemma_62_9_2_Proper

/-!
# Functoriality of proper fibre cycle families

Base change along an arbitrary morphism of bases preserves properness of
families of `r`-cycles on fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open CyclesOnFibers

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 62.9.2: if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is a proper relative `r`-cycle on `X / S`, then any base
change of `α` along `g : S' ⟶ S` is proper. -/
@[stacks 0H62]
theorem proper_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α : CyclesOnFibers f r) (hα : Proper α) :
    Proper (baseChange α g) := sorry

end AlgebraicGeometry
