/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

/-!
# Unibranch local rings

This leaf owns the reduction-normalization presentation of unibranch and
geometrically unibranch local rings.  It deliberately separates the concrete
reduction and normalization data from the Prop-valued local conditions.
-/

@[expose] public section

open Ideal IsLocalRing

universe u

noncomputable section

section

namespace Unibranch

/-- The reduction `A_red` of a commutative ring `A`. -/
@[stacks 0BPZ "reduction"]
abbrev reduction (A : Type u) [CommRing A] :=
  A ⧸ nilradical A

/-- The normalization of `Unibranch.reduction A` in its fraction field. -/
@[stacks 0BPZ "normalization of the reduction"]
abbrev normalization (A : Type u) [CommRing A] :=
  integralClosure (reduction A) (FractionRing (reduction A))

/-- Scoped notation for the reduction `A_red` of a commutative ring `A`. -/
scoped notation:max "(" R ")" "_red" => reduction R

/-- Scoped notation for the unibranch normalization `A'`. -/
scoped postfix:max "′" => normalization

end Unibranch

open scoped Unibranch

variable (A : Type u) [CommRing A]

/-- The unibranch normalization is canonically an `A`-algebra through the
reduction map. -/
@[stacks 0BPZ "algebra structure on the unibranch normalization", instance]
noncomputable instance : Algebra A A′ :=
  ((algebraMap (A)_red A′).comp (algebraMap A (A)_red)).toAlgebra

/-- The reduction and unibranch normalization form the canonical scalar tower. -/
@[stacks 0BPZ "scalar tower through the reduction and normalization", instance]
instance instIsScalarTowerReductionSubtypeFractionRingMemSubalgebraNormalization :
    IsScalarTower A (A)_red A′ := sorry

/-- The unibranch normalization is integral over the original ring. -/
@[stacks 0BPZ "integrality of the unibranch normalization", instance]
instance instIsIntegralSubtypeFractionRingReductionMemSubalgebraNormalization :
    Algebra.IsIntegral A A′ := sorry

variable [IsLocalRing A]

/-- The reduction of a local ring is local. -/
@[stacks 0BPZ "locality of the reduction", instance]
instance instIsLocalRingReduction : IsLocalRing (A)_red := sorry

/-- The reduction map of a local ring is local. -/
@[stacks 0BPZ "locality of the reduction map", instance]
instance instIsLocalHomReductionRingHomAlgebraMap :
    IsLocalHom (algebraMap A (A)_red) := sorry

namespace Unibranch

/-- Every maximal ideal of the normalization contracts to the maximal ideal
of the local base ring. -/
theorem normalization_comap_maximalIdeal
    {m : Ideal A′} (hm : m.IsMaximal) :
    Ideal.comap (algebraMap A A′) m = maximalIdeal A := sorry

/-- The residue-field map induced by the local map from `A` to its unibranch
normalization. -/
@[stacks 0BPZ "residue-field map to a normalization branch"]
noncomputable def normalizationResidueFieldMap
    (m : MaximalSpectrum A′) :
    ResidueField A →+* m.ResidueField :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A A′)
      (normalization_comap_maximalIdeal A m.isMaximal).symm).comp
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).toRingHom

end Unibranch

/-- The residue field at a maximal point of the unibranch normalization is an
algebra over the residue field of the local base ring. -/
@[stacks 0BPZ "residue-field algebra at a normalization branch", instance]
noncomputable instance (m : MaximalSpectrum A′) :
    Algebra (ResidueField A) m.ResidueField :=
  (Unibranch.normalizationResidueFieldMap A m).toAlgebra

/-- A local ring is unibranch when its reduction is a domain and its unibranch
normalization is local. -/
@[stacks 0BPZ "unibranch local rings"]
class IsUnibranch : Prop where
  /-- The reduction has one generic point. -/
  toIsDomain : IsDomain (A)_red
  /-- The normalization of the reduction is local. -/
  isLocalRing_normalization : IsLocalRing A′

/-- The domain and local-normalization conditions characterizing an unibranch
local ring. -/
theorem IsUnibranch.spec [IsUnibranch A] :
    IsDomain (A)_red ∧ IsLocalRing A′ := sorry

/-- A unibranch local ring has domain reduction. -/
@[stacks 0BPZ "domain reduction of a unibranch local ring", instance]
instance instIsDomainReductionOfIsUnibranch [IsUnibranch A] : IsDomain (A)_red := sorry

/-- The unibranch normalization of a unibranch local ring is local. -/
@[stacks 0BPZ "local normalization of a unibranch local ring", instance]
instance IsUnibranch.instIsLocalRingNormalization
    [IsUnibranch A] : IsLocalRing A′ := sorry

/-- The canonical map to the unibranch normalization of a unibranch local
ring is local. -/
@[stacks 0BPZ "local map to the unibranch normalization", instance]
instance IsUnibranch.instIsLocalHomNormalization
    [IsUnibranch A] : IsLocalHom (algebraMap A A′) := sorry

/-- A local ring is geometrically unibranch when it is unibranch and its
induced residue-field extension is purely inseparable. -/
@[stacks 0BPZ "geometrically unibranch local rings"]
class IsGeometricallyUnibranch : Prop where
  /-- The underlying local ring is unibranch. -/
  toIsUnibranch : IsUnibranch A
  /-- The normalization residue extension is purely inseparable. -/
  residueField_isPurelyInseparable :
    -- Local instance justification (instance diamond): the stored parent field must be installed before the global subclass instance is available.
    letI : IsUnibranch A := toIsUnibranch
    IsPurelyInseparable (ResidueField A) (ResidueField A′)

/-- A geometrically unibranch local ring is unibranch. -/
@[stacks 0BPZ "geometrically unibranch implies unibranch", instance]
instance instIsUnibranchOfIsGeometricallyUnibranch [IsGeometricallyUnibranch A] :
    IsUnibranch A := sorry

/-- The unibranch and residue-field conditions characterizing a geometrically
unibranch local ring. -/
theorem IsGeometricallyUnibranch.spec [IsGeometricallyUnibranch A] :
    IsUnibranch A ∧ IsPurelyInseparable (ResidueField A) (ResidueField A′) := sorry

/-- The normalization residue extension of a geometrically unibranch local
ring is purely inseparable. -/
@[stacks 0BPZ "purely inseparable normalization residue extension", instance]
instance IsGeometricallyUnibranch.instIsPurelyInseparableNormalization
    [IsGeometricallyUnibranch A] :
    IsPurelyInseparable (ResidueField A) (ResidueField A′) := sorry

/-- Every field is unibranch. -/
@[stacks 0BPZ "fields are unibranch"]
instance IsUnibranch.field (K : Type u) [Field K] : IsUnibranch K := sorry

/-- Every field is geometrically unibranch. -/
@[stacks 0BPZ "fields are geometrically unibranch"]
instance IsGeometricallyUnibranch.field (K : Type u) [Field K] :
    IsGeometricallyUnibranch K := sorry

end
