/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative scalar actions on principal localizations

The ring map `Localization.awayMap` induces explicit algebra and module actions
between principal localizations.  These actions remain named rather than global
instances because a relative action can conflict with a native action when the
source and target happen to coincide.
-/

@[expose] public section

universe u v w x

namespace Localization.Away.Relative

variable {R : Type u} [CommSemiring R]

variable {S : Type v} [CommSemiring S]

/-- The algebra action on a target principal localization induced by a ring map. -/
@[stacks 051T "relative principal-localization map algebra action"]
noncomputable abbrev mapAlgebra (f : R →+* S) (r : R) :
    Algebra (Localization.Away r) (Localization.Away (f r)) :=
  (Localization.awayMap f r).toAlgebra

/-- The relative algebra action on `S[(f r * s)⁻¹]` obtained by first inverting `r` in
`R` and then adjoining the image of `s`.  This is named support data rather than a global
instance: the same target can carry another ambient algebra action. -/
@[stacks 051T "relative principal-localization product action",
  stacks 077H "077H away-product support action"]
noncomputable abbrev mapMulAlgebra (f : R →+* S) (r : R) (s : S) :
    Algebra (Localization.Away r) (Localization.Away (f r * s)) :=
  ((IsLocalization.Away.awayToAwayRight (f r) s).comp
    (Localization.awayMap f r)).toAlgebra

variable {X : Type w} [AddCommMonoid X]

/-- The action of a source principal localization on any module over the target principal
localization, induced by the map of localizations. -/
@[stacks 051T "relative principal-localization map module action"]
noncomputable abbrev mapModule (f : R →+* S) (r : R)
    [Module (Localization.Away (f r)) X] :
    Module (Localization.Away r) X :=
  Module.compHom X (Localization.awayMap f r)

/-- The two explicit actions induced by a localization map form a scalar tower. -/
@[stacks 051T "relative principal-localization map scalar tower"]
theorem mapModule_isScalarTower (f : R →+* S) (r : R)
    [Module (Localization.Away (f r)) X] :
    -- Local instance justification (instance diamond): the relative algebra action can compete
    -- with another ambient action on the target localization.
    letI : Algebra (Localization.Away r) (Localization.Away (f r)) := mapAlgebra f r
    -- Local instance justification (instance diamond): the source-localized module action is
    -- determined by `f`, not by the target module type alone.
    letI : Module (Localization.Away r) X := mapModule f r
    IsScalarTower (Localization.Away r) (Localization.Away (f r))
      X := sorry

/-- A scalar tower through an intermediate algebra transports to an arbitrary target-localized
module when the base action is the canonical action induced by `Localization.awayMap`.  The
relative actions remain inside the proposition because they need not agree with unrelated ambient
actions on the same types. -/
@[stacks 051T "relative principal-localization intermediate scalar tower"]
theorem mapModule_isScalarTower_of_tower
    (f : R →+* S) (r : R)
    {A : Type x} [CommSemiring A] [Algebra (Localization.Away r) A]
    [Algebra A (Localization.Away (f r))]
    [Module A X] [Module (Localization.Away (f r)) X]
    (h_tower :
      -- Local instance justification (instance diamond): the comparison must use the action
      -- induced by this particular localization map.
      letI : Algebra (Localization.Away r) (Localization.Away (f r)) := mapAlgebra f r
      IsScalarTower (Localization.Away r) A (Localization.Away (f r)))
    [IsScalarTower A (Localization.Away (f r)) X] :
    -- Local instance justification (instance diamond): the source action is induced by `f` and
    -- need not be the ambient action inferred from the module carrier.
    letI : Module (Localization.Away r) X := mapModule f r
    IsScalarTower (Localization.Away r) A X := sorry

variable {M : Type w} [AddCommMonoid M] [Module S M]

variable [Algebra R S]

/-- Under the ambient `R`-algebra structure on `S`, the product-localization action is compatible
with the original scalar action.  Only the relative action is pinned: the canonical `R`-action on
the target localization remains available to avoid an instance diamond. -/
@[stacks 051T "relative principal-localization product scalar tower",
  stacks 077H "077H away-product scalar tower"]
theorem algebraMapMul_isScalarTower (r : R) (s : S) :
    -- Local instance justification (instance diamond): the relative action may conflict with
    -- another ambient action on the same target localization.
    letI : Algebra (Localization.Away r)
        (Localization.Away ((algebraMap R S r) * s)) :=
      mapMulAlgebra (algebraMap R S) r s
    IsScalarTower R (Localization.Away r)
      (Localization.Away ((algebraMap R S r) * s)) := sorry

/-- The relative action of `R_r` on `S_f` induced by the ambient algebra map. -/
@[stacks 051T "relative principal-localization algebra action"]
noncomputable abbrev algebraMapAlgebra (r : R) :
    Algebra (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
  mapAlgebra (algebraMap R S) r

/-- The relative action of `R_r` on `M_f` induced by the ambient algebra map. -/
@[stacks 051T "relative principal-localization module action"]
noncomputable abbrev algebraMapModule (r : R) :
    Module (Localization.Away r) (LocalizedModule.Away (algebraMap R S r) M) :=
  mapModule (X := LocalizedModule.Away (algebraMap R S r) M) (algebraMap R S) r

/-- The relative algebra action on `S_f` is compatible with the maps from `R` and `R_f`. -/
@[stacks 051T "relative principal-localization algebra scalar tower"]
theorem algebraMapAlgebra_isScalarTower (r : R) :
    -- Local instance justification (instance diamond): pin the relative action induced by the
    -- ambient algebra map without registering it globally.
    letI : Algebra (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
      algebraMapAlgebra r
    IsScalarTower R (Localization.Away r) (Localization.Away (algebraMap R S r)) := sorry

/-- Under the canonical relative action on `S_f`, its structural algebra map is precisely the
ring map induced by localizing `R → S`. -/
@[stacks 051T "relative principal-localization algebra map"]
theorem algebraMap_eq_awayMap (r : R) :
    -- Local instance justification (defeq pin): the structural algebra map must unfold to the
    -- explicitly chosen localization map in this equality.
    letI : Algebra (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
      algebraMapAlgebra r
    algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r)) =
      Localization.awayMap (algebraMap R S) r := sorry

/-- The ring map induced by localizing `R → S` sends the canonical image of a coefficient to its
canonical image in the target localization.  This is stated independently of a chosen relative
algebra action, so it is stable across equivalent scalar presentations. -/
@[simp, stacks 051T "relative principal-localization coefficient map"]
theorem awayMap_apply_algebraMap (r s : R) :
    Localization.awayMap (algebraMap R S) r
        (algebraMap R (Localization.Away r) s) =
      algebraMap R (Localization.Away (algebraMap R S r)) s := sorry

end Localization.Away.Relative
