module

-- Import decisions:
-- * `Fiber` and `Fibered` are public because `Fiber`, `IsFibered`, and the Cartesian-lift API
--   occur in the exported owner and reindexing signatures.
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Chosen
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Intrinsic cleavages

A `Functor.Cleavage` chooses strongly cartesian lifts directly on a projection functor.
This leaf owns only that representation-independent data and the bridge to fibredness.
Standard-fibre reindexing is defined in `Cleavage.Basic.Reindex`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

open Functor Fiber

namespace Functor

/- A cleavage is intrinsic data on the projection functor. Standard fibers, alternative
`HasFibers` presentations, and the associated pseudofunctor are views derived from this owner.
The individual lift is bundled so that its source, arrow, and universal property cannot drift
apart. -/

/-- A chosen strongly cartesian lift of `f : V ⟶ p.obj x` with codomain `x`.
Its source automatically lies over `V`, as witnessed by the inherited `IsHomLift`. -/
structure StronglyCartesianLift (p : S ⥤ C) {x : S} {V : C} (f : V ⟶ p.obj x) where
  /-- The source of the chosen lift. -/
  source : S
  /-- The chosen arrow to `x`. -/
  hom : source ⟶ x
  /-- The chosen arrow is strongly cartesian over `f`. -/
  isStronglyCartesian : p.IsStronglyCartesian f hom

attribute [instance] StronglyCartesianLift.isStronglyCartesian

namespace StronglyCartesianLift

variable {p : S ⥤ C} {x : S} {V : C} {f : V ⟶ p.obj x}

/-- The source of a strongly cartesian lift lies over the domain of its base arrow. -/
@[simp]
theorem sourceObj (l : StronglyCartesianLift p f) : p.obj l.source = V := sorry
/- Proof strategy: use the `IsHomLift` instance inherited from `l.isStronglyCartesian` and apply
`IsHomLift.domain_eq p f l.hom`. -/

end StronglyCartesianLift

/-- A cleavage of `p : S ⥤ C` chooses a strongly cartesian lift of
every morphism `f : V ⟶ p.obj x`. The object `x` is implicit because it is already determined
by the codomain of `f`; the resulting lift fits into the commutative square
```
(χ.lift f).source ───────────(χ.lift f).hom──────────▶ x
          │                                               │
        p │                                               │ p
          ▼                                               ▼
          V ─────────────────────f──────────────────────▶ p.obj x
```
and is universal among such lifts. The definition is intrinsic to `p`; it does not commit to the
standard fibers or to any other presentation of them. -/
@[stacks 02XN "cleavage by chosen strongly cartesian lifts"]
structure Cleavage (p : S ⥤ C) where
  /-- The chosen strongly cartesian lift of `f` with codomain `x`. -/
  lift {x : S} {V : C} (f : V ⟶ p.obj x) : StronglyCartesianLift p f

namespace Cleavage

variable {p : S ⥤ C}

/-- A cleavage exhibits its projection as a fibred category. -/
theorem isFibered (χ : p.Cleavage) : p.IsFibered := sorry
/- Proof strategy: apply `IsFibered.of_exists_isStronglyCartesian`; for each requested lift, use
`χ.lift f` and project its `source`, `hom`, and `isStronglyCartesian` fields. -/

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Choose a cleavage directly from mathlib's chosen cartesian lifts on a fibred category.

This is the sole noncanonical choice boundary in the cleavage API. Its return type is the complete,
representation-independent specification: consumers should use `Cleavage.lift`,
`StronglyCartesianLift.source`, `StronglyCartesianLift.hom`, and
`StronglyCartesianLift.isStronglyCartesian`, rather than unfold the choice. No equality with a
different cleavage is asserted. -/
noncomputable def ofIsFibered (p : S ⥤ C) [p.IsFibered] : p.Cleavage where
  lift f :=
    { source := IsPreFibered.pullbackObj rfl f
      hom := IsPreFibered.pullbackMap rfl f
      isStronglyCartesian := IsPreFibered.PullbackMap.stronglyCartesian p f }

/-- A projection admits a cleavage exactly when it is a fibred category. This proposition-level
bridge records both directions without presenting the noncanonical choice `ofIsFibered` as
canonical data. -/
theorem nonempty_iff_isFibered (p : S ⥤ C) :
    Nonempty p.Cleavage ↔ p.IsFibered := sorry
/- Proof strategy: in the forward direction, choose the cleavage and apply `Cleavage.isFibered`;
in the reverse direction, install the supplied `p.IsFibered` proof and use
`Nonempty.intro (Cleavage.ofIsFibered p)`. -/

end Cleavage

end Functor

end CategoryTheory
