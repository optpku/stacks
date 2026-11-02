/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Support of families of fibre cycles under operations

The support of a family of cycles on fibres commutes with base change,
restriction to compatible opens, and flat pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace CyclesOnFibers

/-- The support of a family of fibre cycles after base change along a cartesian
square is the preimage of its support along the map of total spaces. -/
theorem support_baseChange {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : CyclesOnFibers f r) :
    -- Local instance justification (proof-local temporary data): Local finite type of f' follows from hpb and is needed only to type support of the base-changed family.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    support (FiberCycleFamily.baseChange hpb α) = g' ⁻¹' support α :=
  sorry

/-- Membership in the support of a base-changed family of fibre cycles is
membership of the image point in the original support. -/
theorem mem_support_baseChange {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : CyclesOnFibers f r) (x' : X') :
    -- Local instance justification (proof-local temporary data): Local finite type of f' follows from hpb and is needed only to type support of the base-changed family.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    x' ∈ support (FiberCycleFamily.baseChange hpb α) ↔ g' x' ∈ support α :=
  Set.ext_iff.mp (support_baseChange hpb α) x'

/-- Support of a family of fibre cycles after base change along the chosen
pullback square of `f` and `g` is the preimage along `pullback.fst f g`. -/
theorem support_baseChange_pullback {S X S' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (g : S' ⟶ S) {r : ℤ} (α : CyclesOnFibers f r) :
    support (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α) =
      pullback.fst f g ⁻¹' support α :=
  support_baseChange (IsPullback.of_hasPullback f g) α

/-- The support of a family of fibre cycles restricted to compatible opens
is the preimage of the original support along the open immersion. -/
theorem support_restrict {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) {r : ℤ}
    (α : CyclesOnFibers f r) :
    support (FiberCycleFamily.restrict U V hU α) = U.ι ⁻¹' support α :=
  sorry

/-- Membership in the support of a restricted family of fibre cycles is
membership of the image point in the original support. -/
theorem mem_support_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : CyclesOnFibers f r) (u : U.toScheme) :
    u ∈ support (FiberCycleFamily.restrict U V hU α) ↔ U.ι u ∈ support α :=
  Set.ext_iff.mp (support_restrict U V hU α) u

/-- The image of the support of a restricted family of fibre cycles is the
intersection of the original support with `U`. -/
theorem image_support_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : CyclesOnFibers f r) :
    U.ι '' support (FiberCycleFamily.restrict U V hU α) = support α ∩ U :=
  by
    rw [support_restrict U V hU α, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι]

/-- The support of the flat pullback of a family of fibre cycles along a
morphism of relative dimension `e` is the preimage of the original support. -/
theorem support_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e] {r : ℤ}
    (α : CyclesOnFibers f r) :
    support (FiberCycleFamily.flatPullback h hf e α) = h ⁻¹' support α :=
  sorry

/-- Membership in the support of a flat pullback of a family of fibre cycles is
membership of the image point in the original support. -/
theorem mem_support_flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (h : X' ⟶ X) (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    {r : ℤ} (α : CyclesOnFibers f r) (x' : X') :
    x' ∈ support (FiberCycleFamily.flatPullback h hf e α) ↔ h x' ∈ support α :=
  Set.ext_iff.mp (support_flatPullback h hf e α) x'

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
