module

public import stacks_project.Chap62.Lemma_62_5_1_Operations

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

/-- Lemma 62.5.1 (1): base change of a family of fibre cycles is functorial in
pasted cartesian squares. -/
@[stacks 0H4P]
theorem baseChange_comp {S X S' X' S'' X'' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {g₂ : S'' ⟶ S'} {g₂' : X'' ⟶ X'} {f'' : X'' ⟶ S''}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hpb : IsPullback g' f' f g) (hpb' : IsPullback g₂' f'' f' g₂)
    {r : ℤ} (α : f.FiberCycleFamily r) :
    baseChange (hpb'.paste_horiz hpb) α = baseChange hpb' (baseChange hpb α) :=
  sorry

/-- Lemma 62.5.1 (2): restriction of a family of fibre cycles is base change
along the open of the target, followed by flat pullback of relative dimension
zero along the nested open of the source. -/
@[stacks 0H4P]
theorem restrict_eq_flatPullback_baseChange {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : f.FiberCycleFamily r) :
    restrict U V hU α =
      reindex (add_zero r)
        (flatPullback (X.homOfLE hU)
          (resLE_eq_homOfLE_morphismRestrict f U V hU) 0
          (baseChange (isPullback_morphismRestrict f V).flip α)) := sorry

/-- Lemma 62.5.1 (3): flat pullback of a family of fibre cycles commutes with
base change along a cartesian square. -/
@[stacks 0H4P]
theorem flatPullback_baseChange {X' X S S' Y' Y : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f')
    (g : S' ⟶ S) {fY : Y ⟶ S'} {fY' : Y' ⟶ S'} (h' : Y' ⟶ Y)
    (hf' : h' ≫ fY = fY') (gX : Y ⟶ X) (gX' : Y' ⟶ X')
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType fY] [LocallyOfFiniteType fY']
    (hpb : IsPullback gX fY f g) (hpb' : IsPullback gX' fY' f' g)
    (hpbH : IsPullback gX' h' h gX) (e : ℕ)
    [Flat h] [RelativeDimension h e] [Flat h'] [RelativeDimension h' e]
    {r : ℤ} (α : f.FiberCycleFamily r) :
    baseChange hpb' (flatPullback h hf e α) =
      flatPullback h' hf' e (baseChange hpb α) := sorry

/-- Lemma 62.5.1 (4): flat pullback of a family of fibre cycles is functorial,
after reindexing the degree `(r + d) + e = r + (e + d)`. -/
@[stacks 0H4P]
theorem flatPullback_comp {X'' X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} {f'' : X'' ⟶ S}
    (k : X' ⟶ X) (h : X'' ⟶ X') (hk : k ≫ f = f') (hh : h ≫ f' = f'')
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] [LocallyOfFiniteType f'']
    (e d : ℕ) [Flat h] [RelativeDimension h e] [Flat k] [RelativeDimension k d]
    {r : ℤ} (α : f.FiberCycleFamily r) :
    reindex (CycleGroup.flatPullback_comp_degree r e d)
        (flatPullback h hh e (flatPullback k hk d α)) =
      flatPullback (h ≫ k) (triangle_comp hk hh) (e + d) α := sorry

/-- Lemma 62.5.1 (5): proper pushforward of a family of fibre cycles commutes
with base change along a cartesian square. -/
@[stacks 0H4P]
theorem pushforward_baseChange {X Y S S' X' Y' : Scheme.{u}}
    {fX : X ⟶ S} {fY : Y ⟶ S} (h : X ⟶ Y) (hf : h ≫ fY = fX)
    (g : S' ⟶ S) {fX' : X' ⟶ S'} {fY' : Y' ⟶ S'} (h' : X' ⟶ Y')
    (hf' : h' ≫ fY' = fX') (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [LocallyOfFiniteType fX'] [LocallyOfFiniteType fY']
    (hpbX : IsPullback gX fX' fX g) (hpbY : IsPullback gY fY' fY g)
    (hpbH : IsPullback gX h' h gY) [IsProper h] [IsProper h']
    {r : ℤ} (α : fX.FiberCycleFamily r) :
    baseChange hpbY (pushforward h hf α) =
      pushforward h' hf' (baseChange hpbX α) := sorry

/-- Lemma 62.5.1 (6): proper pushforward of a family of fibre cycles is
functorial. -/
@[stacks 0H4P]
theorem pushforward_comp {X Y Z S : Scheme.{u}}
    {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    (h : X ⟶ Y) (k : Y ⟶ Z) (hh : h ≫ fY = fX) (hk : k ≫ fZ = fY)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] [LocallyOfFiniteType fZ]
    [IsProper h] [IsProper k] {r : ℤ} (α : fX.FiberCycleFamily r) :
    pushforward (h ≫ k) (triangle_comp hk hh) α =
      pushforward k hk (pushforward h hh α) := sorry

/-- Lemma 62.5.1 (7): in a cartesian square, proper pushforward of a family of
fibre cycles commutes with flat pullback of relative dimension `e`. -/
@[stacks 0H4P]
theorem pushforward_flatPullback {X Y X' Y' S : Scheme.{u}}
    {fX : X ⟶ S} {fY : Y ⟶ S} {fX' : X' ⟶ S} {fY' : Y' ⟶ S}
    (h : X ⟶ Y) (h' : X' ⟶ Y') (k : Y' ⟶ Y) (k' : X' ⟶ X)
    (hh : h ≫ fY = fX) (hk : k ≫ fY = fY') (hk' : k' ≫ fX = fX')
    (hh' : h' ≫ fY' = fX')
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [LocallyOfFiniteType fX'] [LocallyOfFiniteType fY']
    (hpb : IsPullback k' h' h k) (e : ℕ)
    [IsProper h] [IsProper h'] [Flat k] [Flat k']
    [RelativeDimension k e] [RelativeDimension k' e]
    {r : ℤ} (α : fX.FiberCycleFamily r) :
    flatPullback k hk e (pushforward h hh α) =
      pushforward h' hh' (flatPullback k' hk' e α) := sorry

end FiberCycleFamily
end AlgebraicGeometry.Scheme.Hom
