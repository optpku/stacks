/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite J-0 models of fields

@stack 07PC

The model records a finite domain over a base ring whose fraction field is a
prescribed field.  Compatibility is expressed by an equality of ring maps,
so constructing or consuming a model does not require installing an ambient
algebra diamond.
-/

universe u v

namespace IsJ0Ring

/-- A finite `J-0` domain over `R` whose fraction field is `L`, compatible with a prescribed map
`f : R →+* L`. -/
@[stacks 07PC "finite J-0 fraction-field model"]
structure FiniteFractionModel {R : Type u} [CommRing R]
    {L : Type v} [Field L] (f : R →+* L) where
  /-- The finite domain realizing the model. -/
  carrier : Type v
  /-- The commutative-ring structure on the model. -/
  [commRing : CommRing carrier]
  /-- The model's algebra structure over the base ring. -/
  [algebra : Algebra R carrier]
  /-- Finiteness of the model over the base ring. -/
  [finite : Module.Finite R carrier]
  /-- The prescribed field is an algebra over the model. -/
  [algebraToField : Algebra carrier L]
  /-- The prescribed field is the fraction field of the model. -/
  [fractionRing : IsFractionRing carrier L]
  /-- The two maps from the base ring to the prescribed field agree. -/
  algebraMap_comp : (algebraMap carrier L).comp (algebraMap R carrier) = f
  /-- The model is `J-0`. -/
  [j0 : IsJ0Ring carrier]

namespace FiniteFractionModel

attribute [instance] commRing algebra finite algebraToField fractionRing j0

/-- A finite fraction-field model has a domain as its carrier. -/
instance instIsDomain {R : Type u} [CommRing R] {L : Type v} [Field L]
    {f : R →+* L} (M : FiniteFractionModel f) : IsDomain M.carrier := sorry

/-- Build a finite fraction-field model from an explicit algebra and compatible embedding into
its prescribed fraction field. -/
def of {R : Type u} [CommRing R] {L : Type v} [Field L] {f : R →+* L}
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    [Algebra A L] [IsFractionRing A L] [IsJ0Ring A]
    (h_comp : (algebraMap A L).comp (algebraMap R A) = f) :
    FiniteFractionModel f where
  carrier := A
  commRing := inferInstance
  algebra := inferInstance
  finite := inferInstance
  algebraToField := inferInstance
  fractionRing := inferInstance
  algebraMap_comp := h_comp
  j0 := inferInstance

/-- Elementwise form of compatibility between the base map and the model's fraction-field
embedding. -/
@[simp]
theorem algebraMap_comp_apply {R : Type u} [CommRing R] {L : Type v} [Field L]
    {f : R →+* L} (M : FiniteFractionModel f) (r : R) :
    algebraMap M.carrier L (algebraMap R M.carrier r) = f r := sorry

/-- The finiteness, domain, fraction-field, `J-0`, and map-compatibility properties carried by a
finite fraction-field model. -/
theorem spec {R : Type u} [CommRing R] {L : Type v} [Field L]
    {f : R →+* L} (M : FiniteFractionModel f) :
    Module.Finite R M.carrier ∧ IsDomain M.carrier ∧
      IsFractionRing M.carrier L ∧ IsJ0Ring M.carrier ∧
        (algebraMap M.carrier L).comp (algebraMap R M.carrier) = f := sorry

end FiniteFractionModel

end IsJ0Ring
