/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_13_1_Comp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility of composition of fibre-cycle families with proper pushforward

This file records that forming the composite family of cycles on fibres
commutes with proper pushforward along the top of a cartesian square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.13.6: Let `i : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and
`g : Y' ⟶ Y` form a cartesian square of schemes locally of finite type over
`S`, with `g` proper. Let `α` be a family of `r`-cycles on the fibres of
`X / Y`, and let `β'` be a family of `e`-cycles on the fibres of `Y' / S`.
Then `FiberCycleFamily.pushforward i (hpb.w_assoc p)
(comp (FiberCycleFamily.baseChange hpb α) β')` equals
`comp α (FiberCycleFamily.pushforward g rfl β')`. The source top arrow `f`
is this `i`, the source pullback of `α` is `FiberCycleFamily.baseChange`,
and the source pushforwards are `FiberCycleFamily.pushforward`. -/
@[stacks 0H6N]
theorem comp_pushforward {S X Y X' Y' : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g] [IsProper i]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType (f ≫ p)] [LocallyOfFiniteType (g ≫ p)]
    [LocallyOfFiniteType (f' ≫ g ≫ p)] {r e : ℤ}
    (α : CyclesOnFibers f r) (β' : CyclesOnFibers (g ≫ p) e) :
    FiberCycleFamily.pushforward i (hpb.w_assoc p)
        (comp (FiberCycleFamily.baseChange hpb α) β') =
      comp α (FiberCycleFamily.pushforward g rfl β') := sorry

/-- Evaluating `comp_pushforward` compares coefficients of both sides at a
point of the fibre of `X / S`. -/
theorem comp_pushforward_apply {S X Y X' Y' : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g] [IsProper i]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType (f ≫ p)] [LocallyOfFiniteType (g ≫ p)]
    [LocallyOfFiniteType (f' ≫ g ≫ p)] {r e : ℤ}
    (α : CyclesOnFibers f r) (β' : CyclesOnFibers (g ≫ p) e)
    (s : S) (x : (f ≫ p).fiber s) :
    toAlgebraicCycle
        (FiberCycleFamily.pushforward i (hpb.w_assoc p)
          (comp (FiberCycleFamily.baseChange hpb α) β')) s x =
      toAlgebraicCycle
        (comp α (FiberCycleFamily.pushforward g rfl β')) s x := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
