module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.Pushforward

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

/- Lemma 62.13.6: Let `i : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and
`g : Y' ⟶ Y` form a cartesian square of schemes locally of finite type over
`S`, with `g` proper and `r, e ≥ 0`. Let `α` be a family of `r`-cycles on the fibres of
`X / Y`, and let `β'` be a family of `e`-cycles on the fibres of `Y' / S`.
Then `FiberCycleFamily.pushforward i (hpb.w_assoc p)
(comp (FiberCycleFamily.baseChange hpb α) β')` equals
`comp α (FiberCycleFamily.pushforward g rfl β')`. The source top arrow `f`
is this `i`, the source pullback of `α` is `FiberCycleFamily.baseChange`,
and the source pushforwards are `FiberCycleFamily.pushforward`. -/
@[stacks 0H6N]
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_pushforward :
    ∀ {S X Y X' Y' : Scheme.{u}}
      (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
      (hpb : IsPullback i f' f g) [IsProper g]
      [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
      (α : CyclesOnFibers f (r : ℤ)) (β' : CyclesOnFibers (g ≫ p) (e : ℤ)),
    -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
    letI : IsProper i :=
      MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
    FiberCycleFamily.pushforward i (hpb.w_assoc p)
        (comp (FiberCycleFamily.baseChange hpb α) β') =
      comp α (FiberCycleFamily.pushforward g rfl β'))

/- Evaluating `comp_pushforward` compares coefficients of both sides at a
point of the fibre of `X / S`. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_pushforward_apply :
    ∀ {S X Y X' Y' : Scheme.{u}}
      (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
      (hpb : IsPullback i f' f g) [IsProper g]
      [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
      (α : CyclesOnFibers f (r : ℤ)) (β' : CyclesOnFibers (g ≫ p) (e : ℤ))
      (s : S) (x : (f ≫ p).fiber s),
    -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
    letI : IsProper i :=
      MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
    toAlgebraicCycle
        (FiberCycleFamily.pushforward i (hpb.w_assoc p)
          (comp (FiberCycleFamily.baseChange hpb α) β')) s x =
      toAlgebraicCycle
        (comp α (FiberCycleFamily.pushforward g rfl β')) s x)

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
