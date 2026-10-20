/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Normalization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ramification on branches after DVR base change

The reduced tensor product is the canonical shared owner for the finite product
of fields arising after a finite separable field extension.  This leaf records
the branchwise unramified and tamely ramified consequences without choosing a
product decomposition.

@stack 0EXY
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace DVR.Field.BaseChange

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [hBL : Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1] [Algebra.IsSeparable K K1]

namespace RawBranch

-- Local instance justification (instance diamond): select the right tensor-factor algebra only
-- while constructing raw maximal tensor branches.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The raw tensor-product quotient selected by a maximal ideal. -/
@[stacks 0EXY "raw tensor branch field"]
abbrev ring (m : MaximalSpectrum (K1 ⊗[K] L)) :=
  (K1 ⊗[K] L) ⧸ m.asIdeal

/-- The canonical field structure on a maximal raw tensor-product quotient. -/
@[stacks 0EXY "raw tensor branch field structure"]
noncomputable abbrev fieldInstance (m : MaximalSpectrum (K1 ⊗[K] L)) : Field (ring m) :=
  Ideal.Quotient.field m.asIdeal

/-- Local instance justification (defeq pin): use the quotient commutative-ring structure
underlying this raw tensor-product branch. -/
local instance branchCommRing (m : MaximalSpectrum (K1 ⊗[K] L)) : CommRing (ring m) :=
  Ideal.Quotient.commRing m.asIdeal

/-- The scalar action from the right field factor on a raw tensor branch. -/
@[stacks 0EXY "raw tensor branch fraction-field algebra"]
noncomputable abbrev fractionAlgebra (m : MaximalSpectrum (K1 ⊗[K] L)) :
    Algebra L (ring m) :=
  RingHom.toAlgebra ((Ideal.Quotient.mk m.asIdeal).comp
    (algebraMap L (K1 ⊗[K] L)))

/-- The scalar action from the target DVR on a raw tensor branch. -/
@[stacks 0EXY "raw tensor branch target algebra"]
noncomputable abbrev baseAlgebra (m : MaximalSpectrum (K1 ⊗[K] L)) :
    Algebra B (ring m) :=
  RingHom.toAlgebra ((Ideal.Quotient.mk m.asIdeal).comp
    ((algebraMap L (K1 ⊗[K] L)).comp (algebraMap B L)))

/-- The explicit target-DVR and fraction-field actions on a raw branch form a
scalar tower. -/
@[stacks 0EXY "raw tensor branch scalar tower"]
theorem isScalarTower (m : MaximalSpectrum (K1 ⊗[K] L)) :
    @IsScalarTower B L (ring m) hBL.toSMul
      (fractionAlgebra m).toSMul (baseAlgebra m).toSMul := sorry
-- Proof strategy: apply `IsScalarTower.of_algebraMap_eq'` and extensionalize on `b : B`.
-- Unfold `fractionAlgebra` and `baseAlgebra`; both algebra maps are the same composite through
-- `algebraMap B L`, `Algebra.TensorProduct.includeRight`, and `Ideal.Quotient.mk`, so the goal is
-- reflexive after `RingHom.comp_apply`.

end RawBranch

section RawRamification

-- Local instance justification (instance diamond): select the right tensor-factor action only
-- while presenting the source's raw tensor-product branches.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Lemma 15.115.9 (1) (0EXY): every branch of the raw tensor product is unramified over the
target DVR when the finite separable source extension is unramified. -/
@[stacks 0EXY "unramified raw tensor branches after DVR base change"]
theorem IsUnramified.rawBranch
    (hK1 : DVR.Field.IsUnramified A K K1) (m : MaximalSpectrum (K1 ⊗[K] L)) :
    @DVR.Field.IsUnramified B L (RawBranch.ring m) _ _ _ _ _ _
      (RawBranch.fieldInstance m) (RawBranch.baseAlgebra m)
      (RawBranch.fractionAlgebra m) (RawBranch.isScalarTower m) := sorry
-- Proof strategy: use separability to regard `K1 ⊗[K] L` as its reduced finite product of fields.
-- The maximal quotient `m` selects one field factor.  Compare the integral closure of `B` in that
-- factor with the corresponding normalization branch from
-- `integralClosure.BaseChange.targetFiniteProductOfDedekindDomains`.  Contract each maximal branch
-- to the `K1 / K` normalization, apply `hK1`, and transport residue separability and
-- ramification-index one through the tensor comparison and localized DVR equivalences.

/-- Lemma 15.115.9 (2) (0EXY): every branch of the raw tensor product is tamely ramified over
the target DVR when the finite separable source extension is tamely ramified. -/
@[stacks 0EXY "tamely ramified raw tensor branches after DVR base change"]
theorem IsTamelyRamified.rawBranch
    (hK1 : DVR.Field.IsTamelyRamified A K K1) (m : MaximalSpectrum (K1 ⊗[K] L)) :
    @DVR.Field.IsTamelyRamified B L (RawBranch.ring m) _ _ _ _ _ _
      (RawBranch.fieldInstance m) (RawBranch.baseAlgebra m)
      (RawBranch.fractionAlgebra m) (RawBranch.isScalarTower m) := sorry
-- Proof strategy: use the same maximal-factor and normalization-branch comparison as
-- `IsUnramified.rawBranch`.  Specialize `hK1` on the contracted branch; residue-field separability
-- is preserved by the branch equivalences, while the base-change ramification formula shows that
-- the new index divides the original one.  Therefore it remains coprime to the residue
-- characteristic, giving `DVR.Field.IsTamelyRamified B L (RawBranch.ring m)`.

end RawRamification

/-- Lemma 15.115.9 (1) (0EXY): every branch of the reduced tensor product is
unramified over the target DVR when the finite separable source extension is
unramified. -/
@[stacks 0EXY "unramified branches after DVR base change"]
theorem IsUnramified.branch
    (hK1 : DVR.Field.IsUnramified A K K1)
    (m : MaximalSpectrum (FieldExtension.TensorProduct.reduced K L K1)) :
    let F := FieldExtension.TensorProduct.reduced K L K1 ⧸ m.asIdeal
    let _ : Field F := Ideal.Quotient.field m.asIdeal
    let _ : Algebra B F := inferInstance
    let _ : Algebra L F := inferInstance
    let _ : IsScalarTower B L F := inferInstance
    DVR.Field.IsUnramified B L F := sorry
-- Proof strategy: pull `m` back through
-- `FieldExtension.TensorProduct.tensorEquivReduced` to a maximal ideal of `K1 ⊗[K] L`.  The induced
-- quotient algebra equivalence identifies the packaged reduced branch with `RawBranch.ring` and
-- respects the `B`- and `L`-algebra maps.  Transport `IsUnramified.rawBranch hK1` across this
-- equivalence using invariance of integral closure branches, residue fields, and ramification index.

/-- Lemma 15.115.9 (2) (0EXY): every branch of the reduced tensor product is
tamely ramified over the target DVR when the finite separable source extension
is tamely ramified. -/
@[stacks 0EXY "tamely ramified branches after DVR base change"]
theorem IsTamelyRamified.branch
    (hK1 : DVR.Field.IsTamelyRamified A K K1)
    (m : MaximalSpectrum (FieldExtension.TensorProduct.reduced K L K1)) :
    let F := FieldExtension.TensorProduct.reduced K L K1 ⧸ m.asIdeal
    let _ : Field F := Ideal.Quotient.field m.asIdeal
    let _ : Algebra B F := inferInstance
    let _ : Algebra L F := inferInstance
    let _ : IsScalarTower B L F := inferInstance
    DVR.Field.IsTamelyRamified B L F := sorry
-- Proof strategy: pull `m` back through the same canonical tensor-reduction equivalence as in
-- `IsUnramified.branch`, use the induced quotient algebra equivalence to identify all scalar
-- actions, and transport `IsTamelyRamified.rawBranch hK1`.  Residue separability and the
-- prime-to-characteristic ramification condition are invariant under this algebra equivalence.

end DVR.Field.BaseChange
