/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Induced algebra structures on fraction fields

This leaf owns the canonical algebra structure on fraction fields induced by
an injective map of domains. The structure is deliberately a named value, not
a global instance, because `FractionRing.liftAlgebra` can create algebra
diamonds in ambient typeclass search.
-/

@[expose] public section

namespace FractionRing

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]

/-- The fraction-field algebra structure induced by an injective algebra map
of domains. -/
@[stacks 07ND "fraction-field algebra from an injective map"]
noncomputable abbrev algebraOfInjective (hinj : Function.Injective (algebraMap R S)) :
    Algebra (FractionRing R) (FractionRing S) :=
  -- Local instance justification (proof-local temporary data): `liftAlgebra` needs the
  -- Prop-valued faithful-action witness determined by `hinj` during this construction only.
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  FractionRing.liftAlgebra R (FractionRing S)

/-- The standard algebra action on `FractionRing A` induced from an `R`-algebra `A`
forms a scalar tower with the canonical fraction-ring map.  This is a theorem rather
than an instance, since Mathlib deliberately keeps general scalar-tower search sparse. -/
@[stacks 07ND "fraction-ring canonical scalar tower"]
theorem isScalarTower_algebraMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] :
    IsScalarTower R A (FractionRing A) := sorry

section Transport

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R]
variable [CommRing K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]

/-- The canonical map out of a fraction ring is the transport of a chosen fraction-field model
through `FractionRing.algEquiv`. The algebra structure on the target is
the explicit `FractionRing.liftAlgebra` structure; it is intentionally not installed globally. -/
@[stacks 07ND "fraction-ring algebra-map transport"]
theorem algebraMap_lift_eq_comp_algEquiv [FaithfulSMul R L] :
    @algebraMap (FractionRing R) L _ _ (FractionRing.liftAlgebra R L) =
      (algebraMap K L).comp (FractionRing.algEquiv R K).toRingHom := sorry

end Transport

section Model

variable {A : Type u} {B : Type v} {L : Type w}
variable [CommRing A] [CommRing B] [CommRing L]
variable [Algebra (FractionRing A) L] [Algebra B L] [IsFractionRing B L]

/-- Transport the `FractionRing A`-algebra structure on a chosen fraction-field model `L` back to
`FractionRing B`. This is a named non-instance because it depends on the chosen
model `L`. -/
@[stacks 07ND "fraction-field model scalar transport"]
noncomputable abbrev algebraOfModel : Algebra (FractionRing A) (FractionRing B) :=
  ((FractionRing.algEquiv B L).symm.toRingHom.comp
    (algebraMap (FractionRing A) L)).toAlgebra

/-- The scalar map of `FractionRing.algebraOfModel` is the map to the chosen model followed by
the inverse fraction-field equivalence. -/
@[stacks 07ND "fraction-field model transported scalar map"]
theorem algebraMap_algebraOfModel :
    @algebraMap (FractionRing A) (FractionRing B) _ _
        (algebraOfModel (A := A) (B := B) (L := L)) =
      (FractionRing.algEquiv B L).symm.toRingHom.comp
        (algebraMap (FractionRing A) L) := sorry

end Model

section ModelTower

variable {A : Type u} {B : Type v} {L : Type w}
variable [CommRing A] [CommRing B] [CommRing L]
variable [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
variable [IsFractionRing B L]

/-- The algebra transported by `FractionRing.algebraOfModel` is compatible with the base map. The
algebra structure is pinned locally because different fraction-field models can
induce different structures on the same pair of fraction rings. -/
@[stacks 07ND "fraction-field model scalar tower"]
theorem isScalarTower_algebraOfModel :
    -- Local instance justification (defeq pin): use the explicitly transported algebra structure
    -- selected by `algebraOfModel`, rather than allowing a competing inferred structure.
    letI : Algebra (FractionRing A) (FractionRing B) :=
      algebraOfModel (A := A) (B := B) (L := L)
    -- Local instance justification (defeq pin): derive the module structure from the same
    -- transported algebra so the scalar tower uses its pinned scalar action.
    letI : Module (FractionRing A) (FractionRing B) := Algebra.toModule
    IsScalarTower A (FractionRing A) (FractionRing B) := sorry

end ModelTower

end FractionRing
