/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Proper pushforward and the fibre-cycle action

This file records that the action of a family of cycles on the fibres of a
morphism commutes with proper pushforward along the upper map of a cartesian
square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Let `(S, δ)` be a base scheme with a dimension function, and let
`i : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and `g : Y' ⟶ Y` form a
cartesian square of schemes locally of finite type over `S`, with `g`
proper. For a family `α` of `r`-cycles on the fibres of `f` and a
degree-`e` cycle `β'` on `Y'`, proper pushforward along `i` of the
action of the base-changed family `α` on `β'` equals the
action of `α` on the pushforward of `β'` along `g`. -/
theorem cap_mapHom {S X Y X' Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g] [LocallyOfFiniteType p]
    [LocallyOfFiniteType f] {r e : ℕ}
    (α : CyclesOnFibers f (r : ℤ))
    (β' : CycleGroup Y' ((g ≫ p).relativeDimensionFunction δ) (e : ℤ)) :
    -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
    letI : IsProper i :=
      MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
    CycleGroup.mapHom i
        ((f' ≫ g ≫ p).relativeDimensionFunction δ)
        ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ))
        (cap (g ≫ p) f' δ (FiberCycleFamily.baseChange hpb α) β') =
      cap p f δ α
        (CycleGroup.mapHom g ((g ≫ p).relativeDimensionFunction δ)
          (p.relativeDimensionFunction δ) (e : ℤ) β') :=
  sorry

/-- The equality of the proper-pushforward compatibility of the fibre-cycle
action holds coefficientwise: evaluating both sides at a point of `X`
gives the same integer. -/
theorem cap_mapHom_apply {S X Y X' Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g] [LocallyOfFiniteType p]
    [LocallyOfFiniteType f] {r e : ℕ}
    (α : CyclesOnFibers f (r : ℤ))
    (β' : CycleGroup Y' ((g ≫ p).relativeDimensionFunction δ) (e : ℤ)) (x : X) :
    -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
    letI : IsProper i :=
      MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + (e : ℤ))
        (CycleGroup.mapHom i
          ((f' ≫ g ≫ p).relativeDimensionFunction δ)
          ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ))
          (cap (g ≫ p) f' δ (FiberCycleFamily.baseChange hpb α) β')) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ)
        ((r : ℤ) + (e : ℤ))
        (cap p f δ α
          (CycleGroup.mapHom g ((g ≫ p).relativeDimensionFunction δ)
            (p.relativeDimensionFunction δ) (e : ℤ) β')) x :=
  congrArg (fun c ↦ CycleGroup.toAlgebraicCycle
      ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ)) c x)
    (cap_mapHom δ p f g f' i hpb α β')
end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
