/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Remark_62_5_6_Support

/-!
# Compatibility of support of families of fibre cycles

This file records that the support of a family of cycles on fibres is compatible
with base change, restriction, and flat pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace CyclesOnFibers

/-- Lemma 62.5.7 (1): taking the support of a family of fibre cycles is compatible
with base change along a cartesian square: `support (g*α) = g' ⁻¹' support α`. -/
@[stacks 0H4V]
theorem support_baseChange {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : CyclesOnFibers f r) :
    support (FiberCycleFamily.baseChange hpb α) = g' ⁻¹' support α :=
  sorry

/-- Membership in the support of a base-changed family of fibre cycles is
membership of the image point in the original support. -/
theorem mem_support_baseChange {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : CyclesOnFibers f r) (x' : X') :
    x' ∈ support (FiberCycleFamily.baseChange hpb α) ↔ g' x' ∈ support α :=
  sorry

/-- Support of a family of fibre cycles after base change along the chosen
pullback square of `f` and `g` is the preimage along `pullback.fst f g`. -/
theorem support_baseChange_pullback {S X S' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (g : S' ⟶ S) {r : ℤ} (α : CyclesOnFibers f r) :
    support (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α) =
      pullback.fst f g ⁻¹' support α :=
  sorry

/-- Lemma 62.5.7 (2): taking the support of a family of fibre cycles is compatible
with restriction to compatible opens `U ⊆ X` and `V ⊆ S`:
`support (α|_U) = U.ι ⁻¹' support α`. -/
@[stacks 0H4V]
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
  sorry

/-- The image of the support of a restricted family of fibre cycles is the
intersection of the original support with `U`. -/
theorem image_support_restrict {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : CyclesOnFibers f r) :
    U.ι '' support (FiberCycleFamily.restrict U V hU α) = support α ∩ U :=
  sorry

/-- Lemma 62.5.7 (3): taking the support of a family of fibre cycles is compatible
with flat pullback of relative dimension `e`: `support (h*α) = h ⁻¹' support α`. -/
@[stacks 0H4V]
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
  sorry

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
