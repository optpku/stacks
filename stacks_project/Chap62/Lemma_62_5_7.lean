module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.SupportOperations
import StacksCheckRecall

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

/- Lemma 62.5.7 (1): taking the support of a family of fibre cycles is compatible
with base change along a cartesian square: `support (g*α) = g' ⁻¹' support α`. -/
@[stacks 0H4V] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.support_baseChange :
    ∀ {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
      (hpb : IsPullback g' f' f g) {r : ℤ} (α : CyclesOnFibers f r),
      -- Local instance justification (proof-local temporary data): Local finite type of f' follows from hpb and is needed only to type support of the base-changed family.
      letI : LocallyOfFiniteType f' :=
        MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
      support (FiberCycleFamily.baseChange hpb α) = g' ⁻¹' support α)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.mem_support_baseChange :
  ∀ {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : CyclesOnFibers f r) (x' : X'),
    -- Local instance justification (proof-local temporary data): Local finite type of f' follows from hpb and is needed only to type support of the base-changed family.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    x' ∈ support (FiberCycleFamily.baseChange hpb α) ↔ g' x' ∈ support α)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.support_baseChange_pullback :
  ∀ {S X S' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (g : S' ⟶ S) {r : ℤ} (α : CyclesOnFibers f r),
    support (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α) =
      pullback.fst f g ⁻¹' support α)

/- Lemma 62.5.7 (2): taking the support of a family of fibre cycles is compatible
with restriction to compatible opens `U ⊆ X` and `V ⊆ S`:
`support (α|_U) = U.ι ⁻¹' support α`. -/
@[stacks 0H4V] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.support_restrict :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
      (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) {r : ℤ}
      (α : CyclesOnFibers f r),
      support (FiberCycleFamily.restrict U V hU α) = U.ι ⁻¹' support α)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.mem_support_restrict :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : CyclesOnFibers f r) (u : U.toScheme),
    u ∈ support (FiberCycleFamily.restrict U V hU α) ↔ U.ι u ∈ support α)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.image_support_restrict :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)
    {r : ℤ} (α : CyclesOnFibers f r),
    U.ι '' support (FiberCycleFamily.restrict U V hU α) = support α ∩ U)

/- Lemma 62.5.7 (3): taking the support of a family of fibre cycles is compatible
with flat pullback of relative dimension `e`: `support (h*α) = h ⁻¹' support α`. -/
@[stacks 0H4V] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.support_flatPullback :
    ∀ {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
      [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
      (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e] {r : ℤ}
      (α : CyclesOnFibers f r),
      support (FiberCycleFamily.flatPullback h hf e α) = h ⁻¹' support α)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.mem_support_flatPullback :
  ∀ {X' X S : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (h : X' ⟶ X) (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    {r : ℤ} (α : CyclesOnFibers f r) (x' : X'),
    x' ∈ support (FiberCycleFamily.flatPullback h hf e α) ↔ h x' ∈ support α)

end CyclesOnFibers

end AlgebraicGeometry.Scheme.Hom
