/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Lemma_62_5_1_Operations

/-!
# Compatibility of the fibre-cycle action with proper pushforward

This file records that forming `α ∩ β` commutes with proper pushforward of
the cycle of the base along a cartesian square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.11.6: Let `(S, δ)` be as in the fibre-cycle action setup, and let
`i : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and `g : Y' ⟶ Y` form a cartesian
square of schemes locally of finite type over `S`, with `g` proper. Let `α`
be a family of `r`-cycles on the fibres of `X / Y`, and let `β'` be an
`e`-cycle of `Y'`. Then
`CycleGroup.mapHom i (cap (g ≫ p) f' δ (FiberCycleFamily.baseChange hpb α) β')`
equals `cap p f δ α (CycleGroup.mapHom g β')`. -/
@[stacks 0H6B]
theorem cap_mapHom {S X Y X' Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g] [IsProper i]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    [LocallyOfFiniteType (f ≫ p)] [LocallyOfFiniteType (g ≫ p)]
    [LocallyOfFiniteType (f' ≫ g ≫ p)]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β' : CycleGroup Y' ((g ≫ p).relativeDimensionFunction δ) e) :
    CycleGroup.mapHom i
        ((f' ≫ g ≫ p).relativeDimensionFunction δ)
        ((f ≫ p).relativeDimensionFunction δ) (r + e)
        (cap (g ≫ p) f' δ (FiberCycleFamily.baseChange hpb α) β') =
      cap p f δ α
        (CycleGroup.mapHom g ((g ≫ p).relativeDimensionFunction δ)
          (p.relativeDimensionFunction δ) e β') :=
  sorry

/-- Evaluating `cap_mapHom` compares coefficients of both sides at a point of
`X`. -/
theorem cap_mapHom_apply {S X Y X' Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X)
    (hpb : IsPullback i f' f g) [IsProper g] [IsProper i]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    [LocallyOfFiniteType (f ≫ p)] [LocallyOfFiniteType (g ≫ p)]
    [LocallyOfFiniteType (f' ≫ g ≫ p)]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β' : CycleGroup Y' ((g ≫ p).relativeDimensionFunction δ) e) (x : X) :
    CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ) (r + e)
        (CycleGroup.mapHom i
          ((f' ≫ g ≫ p).relativeDimensionFunction δ)
          ((f ≫ p).relativeDimensionFunction δ) (r + e)
          (cap (g ≫ p) f' δ (FiberCycleFamily.baseChange hpb α) β')) x =
      CycleGroup.toAlgebraicCycle ((f ≫ p).relativeDimensionFunction δ) (r + e)
        (cap p f δ α
          (CycleGroup.mapHom g ((g ≫ p).relativeDimensionFunction δ)
            (p.relativeDimensionFunction δ) e β')) x :=
  sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
