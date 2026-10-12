/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
public import ReasLib.FieldTheory.TensorProduct.Branch
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly unramified base change

This module owns the reusable base-change bridge behind Lemma 15.116.3.  The raw tensor product is
kept as the source field view, while `IsWeakSolutionFor` remains the canonical branchwise owner for
the normalized integral-closure map.

@stack 09ER
@stack 09EY
-/

open scoped TensorProduct
open IsExtensionOfDiscreteValuationRings
open DVR.Field

universe u v w x y z t

namespace DVR.BaseChange

section Tower

variable {A₁ : Type u} {B₁ : Type v} {C₁ : Type w}
variable [CommRing A₁] [CommRing B₁] [CommRing C₁]
variable [IsDomain A₁] [IsDiscreteValuationRing A₁]
variable [IsDomain B₁] [IsDiscreteValuationRing B₁]
variable [IsDomain C₁] [IsDiscreteValuationRing C₁]
variable [Algebra A₁ B₁] [Algebra B₁ C₁]
variable [IsExtensionOfDiscreteValuationRings A₁ B₁]
variable [IsExtensionOfDiscreteValuationRings B₁ C₁]

/-- A normalized three-ring tower whose two adjacent maps are weakly unramified.  The ring
carriers and their DVR structures are parameters of the tower; only the two ramification clauses
are bundled here, so the same object can be reused outside Kummer base change. -/
@[stacks 09EY "weakly unramified normalized tower"]
structure WeaklyUnramifiedTower (A₁ B₁ C₁ : Type*)
    [CommRing A₁] [CommRing B₁] [CommRing C₁]
    [IsDomain A₁] [IsDiscreteValuationRing A₁]
    [IsDomain B₁] [IsDiscreteValuationRing B₁]
    [IsDomain C₁] [IsDiscreteValuationRing C₁]
    [Algebra A₁ B₁] [Algebra B₁ C₁]
    [IsExtensionOfDiscreteValuationRings A₁ B₁]
    [IsExtensionOfDiscreteValuationRings B₁ C₁] : Prop where
  /-- Weak unramifiedness of the first normalized map. -/
  weak_left : WeaklyUnramified A₁ B₁
  /-- Weak unramifiedness of the second normalized map. -/
  weak_right : WeaklyUnramified B₁ C₁

namespace WeaklyUnramifiedTower

/-- The first adjacent weakly unramified clause. -/
@[stacks 09EY "left normalized weak ramification"]
theorem left (h : WeaklyUnramifiedTower A₁ B₁ C₁) :
    WeaklyUnramified A₁ B₁ := sorry
-- Proof strategy: return the `weak_left` field of `h`.

/-- The second adjacent weakly unramified clause. -/
@[stacks 09EY "right normalized weak ramification"]
theorem right (h : WeaklyUnramifiedTower A₁ B₁ C₁) :
    WeaklyUnramified B₁ C₁ := sorry
-- Proof strategy: return the `weak_right` field of `h`.

/-- The two adjacent clauses bundled by `WeaklyUnramifiedTower`. -/
@[stacks 09EY "normalized tower specification"]
theorem spec (h : WeaklyUnramifiedTower A₁ B₁ C₁) :
    WeaklyUnramified A₁ B₁ ∧ WeaklyUnramified B₁ C₁ := sorry
-- Proof strategy: pair `h.left` and `h.right`.

end WeaklyUnramifiedTower

end Tower

section SourceTower

variable {A : Type u} {B : Type v} {C : Type w}
variable {K : Type x} {L : Type y} {M : Type z} {K1 : Type t}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
variable [IsFractionRing C M] [IsScalarTower B C M] [IsScalarTower B L M]
variable [IsScalarTower K L M]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1] [Algebra.IsSeparable K K1]

/-- Lemma 15.116.9: the source integral-closure tower after the separable base change `K₁ / K`.
Its carriers are exactly `integralClosure A K₁`, `integralClosure B (L ⊗[K] K₁)`, and
`integralClosure C (M ⊗[K] K₁)`.  The two algebra structures come from the canonical raw
comparison maps, rather than from arbitrary choices or an implicit identification with reduced
tensor products. -/
@[stacks 09EY "source normalized tower with tensor fields"]
structure SourceTower
    (A : Type u) (B : Type v) (C : Type w) (K : Type x) (L : Type y) (M : Type z) (K1 : Type t)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsExtensionOfDiscreteValuationRings B C]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Field M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
    [IsFractionRing C M] [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower K L M]
    [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
    [FiniteDimensional K K1] [Algebra.IsSeparable K K1] : Prop where
  /-- The source tensor product `L ⊗[K] K₁` is a field. -/
  left_isField : IsField (L ⊗[K] K1)
  /-- The source tensor product `M ⊗[K] K₁` is a field. -/
  right_isField : IsField (M ⊗[K] K1)
  /-- The source integral closure is a domain. -/
  sourceDomain : IsDomain (integralClosure A K1)
  /-- The middle integral closure is a domain. -/
  middleDomain : IsDomain (integralClosure B (L ⊗[K] K1))
  /-- The target integral closure is a domain. -/
  targetDomain : IsDomain (integralClosure C (M ⊗[K] K1))
  /-- The source integral closure is a discrete valuation ring. -/
  sourceDVR : @IsDiscreteValuationRing (integralClosure A K1) inferInstance sourceDomain
  /-- The middle integral closure is a discrete valuation ring. -/
  middleDVR : @IsDiscreteValuationRing (integralClosure B (L ⊗[K] K1)) inferInstance middleDomain
  /-- The target integral closure is a discrete valuation ring. -/
  targetDVR : @IsDiscreteValuationRing (integralClosure C (M ⊗[K] K1)) inferInstance targetDomain
  /-- The canonical first raw comparison is an extension of discrete valuation rings. -/
  leftExtension : @IsExtensionOfDiscreteValuationRings
    (integralClosure A K1) (integralClosure B (L ⊗[K] K1)) inferInstance inferInstance
    (integralClosure.BaseChange.rawAlgebra
      (A := A) (B := B) (K := K) (L := L) (K1 := K1))
    sourceDomain sourceDVR middleDomain middleDVR
  /-- The canonical second raw comparison is an extension of discrete valuation rings. -/
  rightExtension : @IsExtensionOfDiscreteValuationRings
    (integralClosure B (L ⊗[K] K1)) (integralClosure C (M ⊗[K] K1)) inferInstance inferInstance
    (integralClosure.BaseChange.towerAlgebra
      (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1))
    middleDomain middleDVR targetDomain targetDVR
  /-- The two canonical adjacent maps are weakly unramified. -/
  normalized : @WeaklyUnramifiedTower
    (integralClosure A K1) (integralClosure B (L ⊗[K] K1))
    (integralClosure C (M ⊗[K] K1)) inferInstance inferInstance inferInstance
    sourceDomain sourceDVR middleDomain middleDVR targetDomain targetDVR
    (integralClosure.BaseChange.rawAlgebra
      (A := A) (B := B) (K := K) (L := L) (K1 := K1))
    (integralClosure.BaseChange.towerAlgebra
      (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1))
    leftExtension rightExtension

namespace SourceTower

/-- The tensor-field clauses and the literal weakly unramified integral-closure tower bundled by
`SourceTower`. -/
@[stacks 09EY "source normalized tower specification"]
theorem spec
    (h : SourceTower A B C K L M K1) :
    (IsField (L ⊗[K] K1) ∧ IsField (M ⊗[K] K1)) ∧
      @WeaklyUnramifiedTower
        (integralClosure A K1) (integralClosure B (L ⊗[K] K1))
        (integralClosure C (M ⊗[K] K1)) inferInstance inferInstance inferInstance
        h.sourceDomain h.sourceDVR h.middleDomain h.middleDVR h.targetDomain h.targetDVR
        (integralClosure.BaseChange.rawAlgebra
          (A := A) (B := B) (K := K) (L := L) (K1 := K1))
        (integralClosure.BaseChange.towerAlgebra
          (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1))
        h.leftExtension h.rightExtension := sorry
-- Proof strategy: pair the structure fields `h.left_isField` and `h.right_isField`, then return
-- `h.normalized` with the domain, DVR, algebra, and extension arguments fixed by the displayed
-- fields of `h`.

/-- The iterated tensor product used by the second normalized map is a field. -/
@[stacks 09EY "source normalized iterated tensor field"]
theorem composite_isField (h : SourceTower A B C K L M K1) :
    IsField (FieldExtension.TensorProduct.composite K L M K1) := sorry
-- Proof strategy: apply `FieldExtension.TensorProduct.composite_isField_iff.mpr` to
-- `h.right_isField`; the canonical equivalence identifies the iterated tensor product with
-- `M ⊗[K] K1`.

/-- The first canonical map in `SourceTower` is weakly unramified. -/
@[stacks 09EY "source normalized left map"]
theorem left (h : SourceTower A B C K L M K1) :
    @WeaklyUnramified
      (integralClosure A K1) (integralClosure B (L ⊗[K] K1)) inferInstance inferInstance
      (integralClosure.BaseChange.rawAlgebra
        (A := A) (B := B) (K := K) (L := L) (K1 := K1))
      h.sourceDomain h.sourceDVR h.middleDomain h.middleDVR h.leftExtension := sorry
-- Proof strategy: project the left clause from `h.normalized`, keeping the explicit domain, DVR,
-- raw-algebra, and extension fields of `h` as the typeclass arguments.

/-- The second canonical map in `SourceTower` is weakly unramified. -/
@[stacks 09EY "source normalized right maps"]
theorem right (h : SourceTower A B C K L M K1) :
    @WeaklyUnramified
      (integralClosure B (L ⊗[K] K1)) (integralClosure C (M ⊗[K] K1)) inferInstance inferInstance
      (integralClosure.BaseChange.towerAlgebra
        (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1))
      h.middleDomain h.middleDVR h.targetDomain h.targetDVR h.rightExtension := sorry
-- Proof strategy: project the right clause from `h.normalized`, keeping the explicit domain, DVR,
-- tower-algebra, and extension fields of `h` as the typeclass arguments.

/-- The composite weak-solution view supplied by a source tower. -/
@[stacks 09EY "source normalized tower composite"]
theorem toWeakSolution
    [Algebra A C] [IsScalarTower A B C]
    [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M]
    (h : SourceTower A B C K L M K1) :
    -- Local instance justification (proof-local temporary data): derive the composite DVR
    -- extension from the adjacent tower only for this source-facing corollary.
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: use finite separability to identify the raw tensor field `M ⊗[K] K1` with
-- the reduced tensor product, and use its unique maximal branch to identify the chapter branch
-- localizations with the source and target integral closures in `h`; compose `h.left` and
-- `h.right` through ramification-index multiplicativity, then discharge
-- `IsWeakSolutionFor.iff_forall_ideals`.

end SourceTower

end SourceTower

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

/-- Lemma 15.116.3 (2): a finite separable totally ramified field extension has a DVR
integral closure over the base DVR. -/
@[stacks 09ER "totally ramified integral closure DVR"]
theorem integralClosure_isDVR_of_totallyRamified
    [FiniteDimensional K K1] [Algebra.IsSeparable K K1]
    [DVR.Field.IsTotallyRamified A K K1] :
    IsDiscreteValuationRing (integralClosure A K1) := sorry
-- Proof strategy: use finiteness and separability to make the integral closure a Dedekind domain;
-- `DVR.Field.IsTotallyRamified.unique_branch` makes it local, and the Dedekind-local
-- characterization supplies its discrete valuation ring structure.

/-- Lemma 15.116.3 (1): after a finite separable totally ramified base change, the fraction-field
tensor product of a weakly unramified DVR extension is a field. -/
@[stacks 09ER "weakly unramified tensor field"]
theorem tensorField_of_weaklyUnramified_of_totallyRamified
    [FiniteDimensional K K1] [Algebra.IsSeparable K K1]
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified A B]
    [DVR.Field.IsTotallyRamified A K K1] :
    IsField (L ⊗[K] K1) := sorry
-- Proof strategy: decompose the finite separable tensor product into its field branches.  Total
-- ramification gives the unique branch and trivial residue extension over `A`, while weak
-- unramifiedness identifies the mapped maximal ideal over `B`; these facts force the product to
-- have one factor, hence the tensor product is a field.

/-- Lemma 15.116.3 (3): the normalized target integral closure remains a DVR after the same
weakly unramified totally ramified base change. -/
@[stacks 09ER "weakly unramified target domain"]
theorem target_isDomain_of_weaklyUnramified_of_totallyRamified
    [FiniteDimensional K K1] [Algebra.IsSeparable K K1]
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified A B]
    [DVR.Field.IsTotallyRamified A K K1] :
    IsDomain (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) := sorry
-- Proof strategy: obtain `IsField (L ⊗[K] K1)` from
-- `tensorField_of_weaklyUnramified_of_totallyRamified`; finite separability makes the nilradical
-- quotient map an equivalence, so the reduced tensor product is the same field, and its integral
-- closure over the domain `B` is a domain.

/-- Lemma 15.116.3 (3): the normalized target integral closure is a DVR once its canonical
domain structure has been supplied. -/
@[stacks 09ER "weakly unramified target DVR"]
theorem target_isDVR_of_weaklyUnramified_of_totallyRamified
    [FiniteDimensional K K1] [Algebra.IsSeparable K K1]
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified A B]
    [DVR.Field.IsTotallyRamified A K K1]
    (hB : IsDomain (integralClosure B (FieldExtension.TensorProduct.reduced K L K1))) :
    @IsDiscreteValuationRing
      (integralClosure B (FieldExtension.TensorProduct.reduced K L K1)) inferInstance hB := sorry
-- Proof strategy: make the target integral closure Dedekind using finite separability and the
-- tensor-field result; transport the unique maximal branch and residue-field equality supplied by
-- total ramification across weakly unramified base change, then apply the local Dedekind-domain
-- characterization with the explicitly supplied domain witness `hB`.

/-- Lemma 15.116.3 (4): the normalized map is weakly unramified, expressed through the shared
branchwise weak-solution predicate. -/
@[stacks 09ER "weakly unramified normalized map"]
theorem weakSolution_of_weaklyUnramified_of_totallyRamified
    [FiniteDimensional K K1] [Algebra.IsSeparable K K1]
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified A B]
    [DVR.Field.IsTotallyRamified A K K1] :
    IsWeakSolutionFor A B K L K1 := sorry
-- Proof strategy: use the tensor-field theorem to show that the reduced tensor product has one
-- maximal branch; install the source and target DVR structures from the preceding normalization
-- theorems, identify the localized branch map with the canonical base-change map, and use
-- ramification-index preservation to prove its maximal-ideal equality via
-- `IsWeakSolutionFor.iff_map_maximalIdeal`.

end

end DVR.BaseChange

end
