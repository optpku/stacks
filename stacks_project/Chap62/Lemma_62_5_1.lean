module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Compatibilities

/-!
# Compatibilities of operations on families of cycles on fibres

This file records the seven fibrewise compatibilities of base change,
restriction, flat pullback, and proper pushforward for families of cycles on
scheme-theoretic fibres.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberCycleFamily

/- Lemma 62.5.1 (1): base change is functorial for pasted cartesian squares. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange_comp :
  ∀ {S X S' X' S'' X'' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {g₂ : S'' ⟶ S'} {g₂' : X'' ⟶ X'} {f'' : X'' ⟶ S''}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hpb : IsPullback g' f' f g) (hpb' : IsPullback g₂' f'' f' g₂)
    {r : ℤ} (α : f.FiberCycleFamily r),
    baseChange (hpb'.paste_horiz hpb) α = baseChange hpb' (baseChange hpb α))

/- Lemma 62.5.1 (2): restriction combines base change and flat pullback. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.restrict_eq_flatPullback_baseChange :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : f.FiberCycleFamily r),
    restrict U V hU α =
      reindex (add_zero r)
        (flatPullback (X.homOfLE hU)
          (resLE_eq_homOfLE_morphismRestrict f U V hU) 0
          (baseChange (isPullback_morphismRestrict f V).flip α)))

/- Lemma 62.5.1 (3): flat pullback commutes with base change. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.flatPullback_baseChange :
  ∀ {X' X S S' Y' Y : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f')
    (g : S' ⟶ S) {fY : Y ⟶ S'} {fY' : Y' ⟶ S'} (h' : Y' ⟶ Y)
    (hf' : h' ≫ fY = fY') (gX : Y ⟶ X) (gX' : Y' ⟶ X')
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType fY] [LocallyOfFiniteType fY']
    (hpb : IsPullback gX fY f g) (hpb' : IsPullback gX' fY' f' g)
    (hpbH : IsPullback gX' h' h gX) (e : ℕ)
    [Flat h] [RelativeDimension h e]
    {r : ℤ} (α : f.FiberCycleFamily r),
    -- Local instance justification (proof-local temporary data): Flatness of h' depends on hpbH and is needed only to type the base-changed pullback.
    letI : Flat h' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbH inferInstance
    -- Local instance justification (proof-local temporary data): Relative dimension of h' depends on hpbH and is needed only to type the graded base-changed pullback.
    letI : RelativeDimension h' e :=
      (instRelativeDimensionIsStableUnderBaseChange e).of_isPullback hpbH inferInstance
    baseChange hpb' (flatPullback h hf e α) =
      flatPullback h' hf' e (baseChange hpb α))

/- Lemma 62.5.1 (4): flat pullback is functorial with degree reindexing. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.flatPullback_comp :
  ∀ {X'' X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} {f'' : X'' ⟶ S}
    (k : X' ⟶ X) (h : X'' ⟶ X') (hk : k ≫ f = f') (hh : h ≫ f' = f'')
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] [LocallyOfFiniteType f'']
    (e d : ℕ) [Flat h] [RelativeDimension h e] [Flat k] [RelativeDimension k d]
    {r : ℤ} (α : f.FiberCycleFamily r),
    reindex (CycleGroup.flatPullback_comp_degree r e d)
        (flatPullback h hh e (flatPullback k hk d α)) =
      flatPullback (h ≫ k) (triangle_comp hk hh) (e + d) α)

/- Lemma 62.5.1 (5): proper pushforward commutes with base change. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.pushforward_baseChange :
  ∀ {X Y S S' X' Y' : Scheme.{u}}
    {fX : X ⟶ S} {fY : Y ⟶ S} (h : X ⟶ Y) (hf : h ≫ fY = fX)
    (g : S' ⟶ S) {fX' : X' ⟶ S'} {fY' : Y' ⟶ S'} (h' : X' ⟶ Y')
    (hf' : h' ≫ fY' = fX') (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [LocallyOfFiniteType fX'] [LocallyOfFiniteType fY']
    (hpbX : IsPullback gX fX' fX g) (hpbY : IsPullback gY fY' fY g)
    (hpbH : IsPullback gX h' h gY) [IsProper h]
    {r : ℤ} (α : fX.FiberCycleFamily r),
    -- Local instance justification (proof-local temporary data): Properness of h' depends on hpbH and is needed only to type the base-changed pushforward.
    letI : IsProper h' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbH inferInstance
    baseChange hpbY (pushforward h hf α) =
      pushforward h' hf' (baseChange hpbX α))

/- Lemma 62.5.1 (6): proper pushforward is functorial. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.pushforward_comp :
  ∀ {X Y Z S : Scheme.{u}}
    {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    (h : X ⟶ Y) (k : Y ⟶ Z) (hh : h ≫ fY = fX) (hk : k ≫ fZ = fY)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] [LocallyOfFiniteType fZ]
    [IsProper h] [IsProper k] {r : ℤ} (α : fX.FiberCycleFamily r),
    pushforward (h ≫ k) (triangle_comp hk hh) α =
      pushforward k hk (pushforward h hh α))

/- Lemma 62.5.1 (7): proper pushforward commutes with flat pullback. -/
@[stacks 0H4P] #check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.pushforward_flatPullback :
  ∀ {X Y X' Y' S : Scheme.{u}}
    {fX : X ⟶ S} {fY : Y ⟶ S} {fX' : X' ⟶ S} {fY' : Y' ⟶ S}
    (h : X ⟶ Y) (h' : X' ⟶ Y') (k : Y' ⟶ Y) (k' : X' ⟶ X)
    (hh : h ≫ fY = fX) (hk : k ≫ fY = fY') (hk' : k' ≫ fX = fX')
    (hh' : h' ≫ fY' = fX')
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [LocallyOfFiniteType fX'] [LocallyOfFiniteType fY']
    (hpb : IsPullback k' h' h k) (e : ℕ)
    [IsProper h] [Flat k] [RelativeDimension k e]
    {r : ℤ} (α : fX.FiberCycleFamily r),
    -- Local instance justification (proof-local temporary data): Properness of h' depends on hpb and is needed only to type the base-changed pushforward.
    letI : IsProper h' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
    -- Local instance justification (proof-local temporary data): Flatness of k' depends on hpb.flip and is needed only to type the base-changed pullback.
    letI : Flat k' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance
    -- Local instance justification (proof-local temporary data): Relative dimension of k' depends on hpb.flip and is needed only to type the graded base-changed pullback.
    letI : RelativeDimension k' e :=
      (instRelativeDimensionIsStableUnderBaseChange e).of_isPullback hpb.flip inferInstance
    flatPullback k hk e (pushforward h hh α) =
      pushforward h' hh' (flatPullback k' hk' e α))

end FiberCycleFamily
end AlgebraicGeometry.Scheme.Hom
