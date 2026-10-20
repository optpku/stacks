module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 62.11.6: Proper pushforward commutes with the action of a family of
fibre cycles after base change along a cartesian square. -/
@[stacks 0H6B]
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_mapHom :
    ∀ {S X Y X' Y' : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
      [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y)
      (f' : X' ⟶ Y') (i : X' ⟶ X) (hpb : IsPullback i f' f g) [IsProper g]
      [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
      (α : AlgebraicGeometry.Scheme.Hom.CyclesOnFibers f (r : ℤ))
      (β' : AlgebraicGeometry.CycleGroup Y'
        ((g ≫ p).relativeDimensionFunction δ) (e : ℤ)),
      -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
      letI : LocallyOfFiniteType f' :=
        MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
      -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
      letI : IsProper i :=
        MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
      AlgebraicGeometry.CycleGroup.mapHom i
          ((f' ≫ g ≫ p).relativeDimensionFunction δ)
          ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ))
          (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap (g ≫ p) f' δ
            (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange hpb α) β') =
        AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap p f δ α
          (AlgebraicGeometry.CycleGroup.mapHom g
            ((g ≫ p).relativeDimensionFunction δ)
            (p.relativeDimensionFunction δ) (e : ℤ) β'))

/- The coefficientwise evaluation of the shared-owner compatibility theorem. -/
-- Lemma 62.11.6 (coefficient consequence)
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_mapHom_apply :
    ∀ {S X Y X' Y' : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
      [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y) (g : Y' ⟶ Y)
      (f' : X' ⟶ Y') (i : X' ⟶ X) (hpb : IsPullback i f' f g) [IsProper g]
      [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
      (α : AlgebraicGeometry.Scheme.Hom.CyclesOnFibers f (r : ℤ))
      (β' : AlgebraicGeometry.CycleGroup Y'
        ((g ≫ p).relativeDimensionFunction δ) (e : ℤ)) (x : X),
      -- Local instance justification (search instability): finite type of `f'` follows from the explicit arbitrary-square witness `hpb`, which ordinary typeclass search cannot recover.
      letI : LocallyOfFiniteType f' :=
        MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
      -- Local instance justification (search instability): properness of `i` follows from `hpb.flip` and `IsProper g`; the explicit arbitrary-square witness is unavailable to ordinary instance search.
      letI : IsProper i :=
        MorphismProperty.of_isPullback (P := @IsProper) hpb.flip inferInstance
      AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ))
          (AlgebraicGeometry.CycleGroup.mapHom i
            ((f' ≫ g ≫ p).relativeDimensionFunction δ)
            ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ))
            (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap (g ≫ p) f' δ
              (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange hpb α) β')) x =
        AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          ((f ≫ p).relativeDimensionFunction δ) ((r : ℤ) + (e : ℤ))
          (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap p f δ α
            (AlgebraicGeometry.CycleGroup.mapHom g
              ((g ≫ p).relativeDimensionFunction δ)
              (p.relativeDimensionFunction δ) (e : ℤ) β')) x)
