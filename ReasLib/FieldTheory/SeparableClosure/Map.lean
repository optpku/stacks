/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Map-oriented relative separable closures

Mathlib's relative separable closure is indexed by an `Algebra` structure.
This leaf gives the same construction a map-oriented owner when an explicit
field homomorphism is the primary datum.  It also records the functorial
containment needed to compare relative separable closures in one common field.
-/

universe u v w x y

namespace RingHom

variable {F : Type u} {E : Type v} {K : Type w}
variable [Field F] [Field E] [Field K]

/-- The relative separable closure in `K` determined by an explicit field map
`j : F →+* K`.

The map-oriented construction is a `Subfield K`, rather than an
`IntermediateField F K`: the latter stores an ambient `Algebra F K` instance,
whereas this API deliberately takes that structure as explicit map data. -/
@[stacks 04GW "map-oriented relative separable closure"]
noncomputable def separableClosure
    (j : F →+* K) : Subfield K :=
  let A : Algebra F K := RingHom.toAlgebra j
  (@_root_.separableClosure F K _ _ A).toSubfield

/-- The field range of an explicit field map lies in its relative separable
closure. -/
@[stacks 04GW "field range in a map-oriented separable closure"]
theorem fieldRange_le_separableClosure
    (j : F →+* K) :
    j.fieldRange ≤ j.separableClosure := sorry

/-- A commuting triangle of field maps induces an inclusion between the two
relative separable closures inside the common target field. -/
@[stacks 04GW "functoriality of map-oriented separable closures"]
theorem separableClosure_le_of_comp_eq
    (f : F →+* E) (target : E →+* K) (source : F →+* K)
    (comm : target.comp f = source) :
    source.separableClosure ≤ target.separableClosure := sorry

/-- The map-oriented form of the assertion that the target of a field map is
a separable closure of its source.  It uses the algebra structure determined
by the map, so callers need not install a temporary global instance. -/
@[stacks 04GW "map-oriented separable closure"]
abbrev IsSepClosure (f : F →+* E) : Prop :=
  let A : Algebra F E := RingHom.toAlgebra f
  @_root_.IsSepClosure F _ E _ A

namespace SeparableClosure

/-- A realization of the relative separable closure of a field map inside an
explicit common field.  The structure stores the two field maps and their
factorization; no local-ring presentation is part of this field-theoretic
owner. -/
@[stacks 04GW "relative separable-closure realization"]
structure Realization (f : F →+* E) where
  /-- The map whose relative separable closure is being realized. -/
  baseMap : F →+* K
  /-- The realization of the target field inside the common field. -/
  lift : E →+* K
  /-- The realization factors the prescribed base-field map through `f`. -/
  comm : lift.comp f = baseMap
  /-- The realization has exactly the relative separable closure of `baseMap`
  as field range. -/
  fieldRange_eq :
    lift.fieldRange = RingHom.separableClosure baseMap

namespace Realization

variable {f : F →+* E}

/-- Constructs a relative separable-closure realization from its two maps and
the equations they satisfy. -/
def ofMaps
    (baseMap : F →+* K) (lift : E →+* K)
    (comm : lift.comp f = baseMap)
    (fieldRange_eq : lift.fieldRange = RingHom.separableClosure baseMap) :
    Realization (K := K) f :=
  { baseMap, lift, comm, fieldRange_eq }

/-- The target field in a relative separable-closure realization is identified
with the corresponding subfield of the common field. -/
@[stacks 04GW "field equivalence from a separable-closure realization"]
noncomputable def liftEquiv
    (model : Realization (K := K) f) :
    E ≃+* RingHom.separableClosure model.baseMap :=
  model.lift.rangeRestrictFieldEquiv.trans
    (RingEquiv.subfieldCongr model.fieldRange_eq)

/-- Coercing `liftEquiv` into the common field recovers the realization map. -/
@[simp, stacks 04GW "realization equivalence in the common field"]
theorem liftEquiv_apply_coe
    (model : Realization (K := K) f) (x : E) :
    (model.liftEquiv x : K) = model.lift x := sorry

/-- The factorization and field-range conditions defining a relative
separable-closure realization. -/
@[stacks 04GW "relative separable-closure realization specification"]
theorem spec
    (model : Realization (K := K) f) :
    model.lift.comp f = model.baseMap ∧
      model.lift.fieldRange =
        RingHom.separableClosure model.baseMap := sorry

/-- A field map whose target is a separable closure admits a realization in
every separably closed common field, for each prescribed base-field map.  The
realization is existential because the identification of separable closures is
not canonical. -/
@[stacks 04GW "existence of a relative separable-closure realization"]
theorem exists_of_isSepClosure
    (f : F →+* E) (hf : RingHom.IsSepClosure f)
    [IsSepClosed K]
    (baseMap : F →+* K) :
    ∃ model : Realization (K := K) f,
      model.baseMap = baseMap := sorry

end Realization

namespace Realization

section RangeFactorization

variable {F1 : Type u} {E1 : Type v} {K : Type w}
variable {F2 : Type x} {E2 : Type y}
variable [Field F1] [Field E1] [Field F2] [Field E2] [Field K]
variable {f : F1 →+* E1} {g : F2 →+* E2}

/-- Factor one relative separable-closure realization through another when
the first realization has field range contained in the second. -/
@[stacks 04GW "comparison map from separable-closure realizations"]
noncomputable def mapOfRangeLe
    (source : Realization (K := K) f) (target : Realization (K := K) g)
    (h : source.lift.fieldRange ≤ target.lift.fieldRange) :
    E1 →+* E2 :=
  target.lift.rangeRestrictFieldEquiv.symm.toRingHom.comp
    ((Subfield.inclusion h).comp source.lift.rangeRestrictField)

/-- The field map induced by a range inclusion is characterized by its
commutation with the two realization maps into the common field. -/
@[stacks 04GW "comparison-map specification for separable-closure realizations"]
theorem lift_comp_mapOfRangeLe
    (source : Realization (K := K) f) (target : Realization (K := K) g)
    (h : source.lift.fieldRange ≤ target.lift.fieldRange) :
    target.lift.comp (mapOfRangeLe source target h) = source.lift := sorry

end RangeFactorization

section CommonField

variable {R : Type u} {S : Type v} {A : Type x} {B : Type y} {K : Type w}
variable [Field R] [Field S] [Field A] [Field B] [Field K]
variable {base : R →+* S} {source : R →+* A} {target : S →+* B}

/-- Two relative separable-closure realizations in one common field determine
a unique compatible field map over a commuting cospan. -/
@[stacks 04GW "compatible map between separable-closure realizations"]
theorem existsUniqueCompatible
    (sourceModel : Realization (K := K) source)
    (targetModel : Realization (K := K) target)
    (base_comm : targetModel.baseMap.comp base = sourceModel.baseMap) :
    ∃! comparison : A →+* B,
      comparison.comp source = target.comp base ∧
        targetModel.lift.comp comparison = sourceModel.lift := sorry

end CommonField

end Realization

end SeparableClosure

end RingHom
