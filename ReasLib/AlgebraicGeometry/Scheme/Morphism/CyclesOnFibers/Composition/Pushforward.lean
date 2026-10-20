module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap.Pushforward

/-!
# Proper pushforward and composition of fibre-cycle families

Composition of families of cycles on fibres commutes with proper pushforward
along the upper map of a cartesian square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- Let `i : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and `g : Y' ⟶ Y`
form a cartesian square over a scheme `S`, with `g` proper and `p : Y ⟶ S`
and `f` locally of finite type. For nonnegative degrees `r` and `e`, pushing
forward along `i` the composition of the base change of an `r`-cycle family
on `X / Y` with an `e`-cycle family on `Y' / S` equals composing the original
family with the pushforward along `g` of the second family. -/
theorem comp_pushforward {S X Y X' Y' : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : CyclesOnFibers f (r : ℤ)) (β' : CyclesOnFibers (g ≫ p) (e : ℤ)) :
    -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
    letI : IsProper i :=
      MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
    FiberCycleFamily.pushforward i (hpb.w_assoc p)
        (comp (FiberCycleFamily.baseChange hpb α) β') =
      comp α (FiberCycleFamily.pushforward g rfl β') := sorry

/-- Proper pushforward compatibility for composition of fibre-cycle families
holds coefficientwise at every point of every fibre of `X / S`. -/
theorem comp_pushforward_apply {S X Y X' Y' : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : CyclesOnFibers f (r : ℤ)) (β' : CyclesOnFibers (g ≫ p) (e : ℤ))
    (s : S) (x : (f ≫ p).fiber s) :
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
        (comp α (FiberCycleFamily.pushforward g rfl β')) s x := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
