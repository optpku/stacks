/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Kummer.FiniteLevel
public import ReasLib.FieldTheory.TensorProduct.Branch
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct
open scoped Algebra.TensorProduct.Right

namespace KummerArtinSchreier
namespace FiniteLevel

universe uB u v w u'

/-!
# Kummer finite levels after tensor-product base change

The generic branch is owned by `FieldExtension.TensorProduct.Branch`.  This file specializes it to
Kummer--Artin--Schreier finite levels and centralizes the quotient-field and tensor-algebra pins
needed by downstream statements.

@stack 09F4
@stack 09F5
-/

/-!
The support below separates the normalization witnesses from the Kummer finite-level property.
Both branch and global base-change predicates use the same tower owner; only their canonical base
algebra and carriers differ.
-/

/-- A normalized field tower over a coefficient ring.  The algebra structures are explicit pins so
the normalization carrier is stable under tensor-product instance diamonds. -/
@[stacks 09F4 "normalized field-tower support", stacks 09F5 "normalized field-tower support"]
structure Normalization
    (B : Type uB) [CommRing B]
    (F : Type u) [CommRing F]
    (E : Type v) [CommRing E]
    (baseAlgebra : Algebra B F) (extensionAlgebra : Algebra F E) : Prop where
  /-- The normalization's fraction-field carrier is a field. -/
  baseField : IsField F
  /-- The extension carrier is a field. -/
  extensionField : IsField E
  /-- The selected field is the fraction field of the integral closure. -/
  fractionRing :
    -- Local instance justification (proof-local temporary data): install the field structure
    -- stored by this support only while interpreting its fraction-ring witness.
    let _ : Field F := baseField.toField
    -- Local instance justification (instance diamond): pin the explicitly selected base algebra
    -- instead of choosing among the tensor-product algebra structures globally.
    let _ : Algebra B F := baseAlgebra
    IsFractionRing (integralClosure B F) F
  /-- The integral closure is a discrete valuation ring. -/
  dvr :
    -- Local instance justification (proof-local temporary data): use the stored field witness only
    -- while forming the normalization carrier.
    let _ : Field F := baseField.toField
    -- Local instance justification (instance diamond): the normalization belongs to the selected
    -- base algebra, which must not become a global tensor-product instance.
    let _ : Algebra B F := baseAlgebra
    IsDiscreteValuationRing (integralClosure B F)

namespace Normalization

/-- The finite-level property carried by a normalized field tower.  The fraction-ring witness is
explicit in the proposition, so it is not lost when the owner is reused downstream. -/
@[stacks 09F4 "finite-level property of normalized support"]
def IsExtension
    {B : Type uB} [CommRing B]
    {F : Type u} [CommRing F]
    {E : Type v} [CommRing E]
    {baseAlgebra : Algebra B F} {extensionAlgebra : Algebra F E}
    (N : Normalization B F E baseAlgebra extensionAlgebra)
    (p : ℕ) [Fact p.Prime] : Prop :=
  -- Local instance justification (proof-local temporary data): recover the field carried by `N`
  -- only while interpreting its finite-level property.
  let _ : Field F := N.baseField.toField
  -- Local instance justification (proof-local temporary data): recover the extension field carried
  -- by `N` only inside this predicate.
  let _ : Field E := N.extensionField.toField
  -- Local instance justification (instance diamond): pin the base action selected by `N` rather
  -- than exporting a competing tensor-product algebra.
  let _ : Algebra B F := baseAlgebra
  -- Local declaration justification (abbreviation): name the canonical normalization carrier used
  -- in both conjuncts of this predicate.
  let BF := integralClosure B F
  -- Local instance justification (defeq pin): expose the fraction-field witness carried by the
  -- normalization while forming the source predicate, rather than rebuilding a competing one.
  letI : IsFractionRing BF F := N.fractionRing
  IsFractionRing BF F ∧
    @KummerArtinSchreier.FiniteLevel.IsExtension BF _ N.dvr.toIsLocalRing F
      N.baseField.toField (RingHom.toAlgebra BF.val.toRingHom) E N.extensionField.toField
      extensionAlgebra p inferInstance

/-- The exact-level property carried by a normalized field tower. -/
@[stacks 09F5 "exact-level property of normalized support"]
def IsAtLevel
    {B : Type uB} [CommRing B]
    {F : Type u} [CommRing F]
    {E : Type v} [CommRing E]
    {baseAlgebra : Algebra B F} {extensionAlgebra : Algebra F E}
    (N : Normalization B F E baseAlgebra extensionAlgebra)
    (p : ℕ) (l : ℚ) [Fact p.Prime] : Prop :=
  -- Local instance justification (proof-local temporary data): recover the field carried by `N`
  -- only while interpreting its exact level.
  let _ : Field F := N.baseField.toField
  -- Local instance justification (proof-local temporary data): recover the extension field carried
  -- by `N` only inside this predicate.
  let _ : Field E := N.extensionField.toField
  -- Local instance justification (instance diamond): pin the base action selected by `N` rather
  -- than exporting a competing tensor-product algebra.
  let _ : Algebra B F := baseAlgebra
  -- Local declaration justification (abbreviation): name the canonical normalization carrier used
  -- by the exact-level owner.
  let BF := integralClosure B F
  @KummerArtinSchreier.FiniteLevel.IsAtLevel BF _ inferInstance N.dvr F
    N.baseField.toField (RingHom.toAlgebra BF.val.toRingHom) N.fractionRing E
    N.extensionField.toField extensionAlgebra p l inferInstance

end Normalization

/-- The composite algebra on the residue field selected by a tensor branch. -/
@[stacks 09F4 "branch normalization base algebra"]
noncomputable abbrev branchBaseAlgebra
    {B : Type uB} [CommRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L]
    {M : Type w} [Field M] [Algebra L M]
    {K1 : Type u'} [Field K1] [Algebra K K1]
    (b : FieldExtension.TensorProduct.Branch K L M K1) : Algebra B b.field :=
  RingHom.toAlgebra ((algebraMap L b.field).comp (algebraMap B L))

/-- Normalization support selected by a reduced tensor branch. -/
@[stacks 09F4 "branch normalization support"]
abbrev BranchNormalization
    {B : Type uB} [CommRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L]
    {M : Type w} [Field M] [Algebra L M]
    {K1 : Type u'} [Field K1] [Algebra K K1]
    (b : FieldExtension.TensorProduct.Branch K L M K1) : Prop :=
  Normalization B b.field b.extension (branchBaseAlgebra (B := B) b)
    Algebra.TensorProduct.rightAlgebra

/-- The composite algebra on a tensor-product base field. -/
@[stacks 09F4 "global normalization base algebra"]
abbrev tensorBaseAlgebra
    (B : Type uB) (K : Type u) (L : Type v)
    [CommRing B] [Field K] [Field L] [Algebra B L] [Algebra K L]
    (K1 : Type u') [Field K1] [Algebra K K1] :
    Algebra B (FieldExtension.TensorProduct.baseChange K L K1) :=
  RingHom.toAlgebra
    ((algebraMap L (FieldExtension.TensorProduct.baseChange K L K1)).comp (algebraMap B L))

/-- Normalization support for a global tensor-product base change. -/
@[stacks 09F4 "global normalization support"]
abbrev BaseChangeNormalization
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [Algebra L M]
    (K1 : Type u') [Field K1] [Algebra K K1] : Prop :=
  Normalization B (FieldExtension.TensorProduct.baseChange K L K1)
    (FieldExtension.TensorProduct.composite K L M K1) (tensorBaseAlgebra B K L K1)
    Algebra.TensorProduct.rightAlgebra

namespace IsExtension

variable {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
variable [Field K] [Field L] [Field M] [Field K1]
variable [Algebra K L] [Algebra K K1] [Algebra L M]

/-- The finite-level owner induced by a branch and its normalized field-tower support. -/
@[stacks 09F4 "finite-level owner on a reduced tensor branch"]
def OnBranch
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1) : Prop :=
  ∃ N : BranchNormalization (B := B) b, N.IsExtension p

namespace OnBranch

/-- A branch predicate exposes its normalization support. -/
@[stacks 09F4 "finite-level branch specification and constructor"]
theorem spec
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1)
    (h : OnBranch (B := B) p b) :
    ∃ N : BranchNormalization (B := B) b, N.IsExtension p := sorry
-- Proof strategy: unfold `IsExtension.OnBranch`; this is its defining existential.

/-- Construct a branch predicate from normalization support. -/
@[stacks 09F4 "finite-level branch constructor"]
theorem of_spec
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1)
    (N : BranchNormalization (B := B) b) (hN : N.IsExtension p) :
    OnBranch (B := B) p b := sorry
-- Proof strategy: unfold `IsExtension.OnBranch` and choose `N` with witness `hN`.

end OnBranch

end IsExtension

namespace IsAtLevel

variable {K : Type u} {L : Type v} {M : Type w} {K1 : Type u'}
variable [Field K] [Field L] [Field M] [Field K1]
variable [Algebra K L] [Algebra K K1] [Algebra L M]

/-- The exact-level owner induced by a branch and its normalized field-tower support. -/
@[stacks 09F5 "exact finite-level owner on a reduced tensor branch"]
def OnBranch
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1) : Prop :=
  ∃ N : BranchNormalization (B := B) b, N.IsAtLevel p l

namespace OnBranch

/-- The exact-level branch predicate exposes its normalization support. -/
@[stacks 09F5 "exact finite-level branch specification and constructor"]
theorem spec
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1)
    (h : OnBranch (B := B) p l b) :
    ∃ N : BranchNormalization (B := B) b, N.IsAtLevel p l := sorry
-- Proof strategy: unfold `IsAtLevel.OnBranch`; this is its defining existential.

/-- Construct an exact-level branch predicate from normalization support. -/
@[stacks 09F5 "exact finite-level branch constructor"]
theorem of_spec
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1)
    (N : BranchNormalization (B := B) b) (hN : N.IsAtLevel p l) :
    OnBranch (B := B) p l b := sorry
-- Proof strategy: unfold `IsAtLevel.OnBranch` and choose `N` with witness `hN`.

end OnBranch

end IsAtLevel

namespace IsExtension.OnBranch

/-- Every finite-level branch realizes a unique rational level. -/
@[stacks 09F5 "existence of the level on a finite-level branch"]
theorem exists_level
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1) :
    IsExtension.OnBranch (B := B) p b →
      ∃ l : ℚ, IsAtLevel.OnBranch (B := B) p l b := sorry
-- Proof strategy: unpack the normalization support `N`.  Install its stored field, algebra, DVR,
-- and fraction-ring pins only inside the proof, apply the inner `FiniteLevel.IsExtension.exists_level`,
-- and package the resulting `l` with the same `N` as an `IsAtLevel.OnBranch` witness.

end IsExtension.OnBranch

namespace IsAtLevel.OnBranch

/-- Forgetting the exact level of a branch gives its finite-level extension property. -/
@[stacks 09F5 "forgetting the level on a finite-level branch"]
theorem toExtension
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1) :
    IsAtLevel.OnBranch (B := B) p l b → IsExtension.OnBranch (B := B) p b := sorry
-- Proof strategy: unpack the shared normalization `N`, apply the inner
-- `FiniteLevel.IsAtLevel.toExtension`, retain `N.fractionRing`, and repackage the same support as
-- `IsExtension.OnBranch`.

/-- The exact level carried by a fixed reduced tensor-product branch is unique. -/
@[stacks 09F5 "uniqueness of the level on a finite-level branch"]
theorem unique
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra K K1] [Algebra L M]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) {l l' : ℚ} [Fact p.Prime]
    (b : FieldExtension.TensorProduct.Branch K L M K1) :
    IsAtLevel.OnBranch (B := B) p l b →
      IsAtLevel.OnBranch (B := B) p l' b → l = l' := sorry
-- Proof strategy: unpack both normalization witnesses.  Their stored field, algebra, fraction-ring,
-- and DVR proofs are propositionally unique on the fixed branch carriers; align those pins by
-- proof irrelevance and apply the inner `FiniteLevel.IsAtLevel.unique`.

end IsAtLevel.OnBranch

namespace IsExtension

/-- The global base-change owner induced by normalized tensor fields. -/
@[stacks 09F4 "global finite-level base-change owner"]
def OnBaseChange
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1] : Prop :=
  ∃ N : BaseChangeNormalization B K L M K1, N.IsExtension p

namespace OnBaseChange

/-- The global base-change predicate exposes its normalization support. -/
@[stacks 09F4 "global base-change specification and constructor"]
theorem spec
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1]
    (h : OnBaseChange B K L M p K1) :
    ∃ N : BaseChangeNormalization B K L M K1, N.IsExtension p := sorry
-- Proof strategy: unfold `IsExtension.OnBaseChange`; this is its defining existential.

/-- Construct a global base-change predicate from normalization support. -/
@[stacks 09F4 "global base-change constructor"]
theorem of_spec
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1]
    (N : BaseChangeNormalization B K L M K1) (hN : N.IsExtension p) :
    OnBaseChange B K L M p K1 := sorry
-- Proof strategy: unfold `IsExtension.OnBaseChange` and choose `N` with witness `hN`.

end OnBaseChange

/-- A finite-level extension after base change is witnessed by one reduced tensor branch. -/
@[stacks 09F4 "finite-level branch after base change"]
def AfterBaseChange
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1] : Prop :=
  ∃ b : FieldExtension.TensorProduct.Branch K L M K1,
    IsExtension.OnBranch (B := B) p b

/-- A global finite-level base change has a canonical reduced tensor-product branch view. -/
@[stacks 09F4 "global-to-branch finite-level bridge"]
theorem OnBaseChange.toAfterBaseChange
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    {K1 : Type*} [Field K1] [Algebra K K1]
    (h : OnBaseChange B K L M p K1) :
    AfterBaseChange B K L M p K1 := sorry
-- Proof strategy: unpack the global normalization `N`.  Its field structures make the reduced base
-- change a field and the iterated composite a field, so choose the unique maximal branch of the
-- reduced field.  Use `tensorEquivReduced`, `Branch.quotientFieldEquiv`, and
-- `compositeEquivBaseChange` to transport the normalization, DVR, fraction-ring, and inner
-- finite-level witnesses to that branch, then package `IsExtension.OnBranch`.

end IsExtension

namespace IsAtLevel

/-- The exact-level global base-change owner induced by normalized tensor fields. -/
@[stacks 09F5 "global exact finite-level base-change owner"]
def OnBaseChange
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1] : Prop :=
  ∃ N : BaseChangeNormalization B K L M K1, N.IsAtLevel p l

namespace OnBaseChange

/-- The exact-level global base-change predicate exposes its normalization support. -/
@[stacks 09F5 "exact global base-change specification and constructor"]
theorem spec
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1]
    (h : OnBaseChange B K L M p l K1) :
    ∃ N : BaseChangeNormalization B K L M K1, N.IsAtLevel p l := sorry
-- Proof strategy: unfold `IsAtLevel.OnBaseChange`; this is its defining existential.

/-- Construct an exact-level global base-change predicate from normalization support. -/
@[stacks 09F5 "exact global base-change constructor"]
theorem of_spec
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M]
    [Algebra B L] [Algebra K L] [IsFractionRing B L]
    [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1]
    (N : BaseChangeNormalization B K L M K1) (hN : N.IsAtLevel p l) :
    OnBaseChange B K L M p l K1 := sorry
-- Proof strategy: unfold `IsAtLevel.OnBaseChange` and choose `N` with witness `hN`.

end OnBaseChange

/-- An exact finite-level extension after base change is witnessed by one reduced tensor branch. -/
@[stacks 09F5 "exact finite-level branch after base change"]
def AfterBaseChange
    (B : Type uB) (K : Type u) (L : Type v) (M : Type w)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Field M] [Algebra L M]
    (p : ℕ) (l : ℚ) [Fact p.Prime]
    (K1 : Type*) [Field K1] [Algebra K K1] : Prop :=
  ∃ b : FieldExtension.TensorProduct.Branch K L M K1,
    IsAtLevel.OnBranch (B := B) p l b

namespace AfterBaseChange

/-- Forgetting the exact level on a branch base change gives the unrefined base-change view. -/
@[stacks 09F5 "forgetting the level after branch base change"]
theorem toExtension
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K] {L : Type v} [Field L]
    {M : Type w} [Field M] {K1 : Type u'} [Field K1]
    [Algebra K L] [Algebra L M]
    [Algebra K K1]
    [Algebra B L] [IsFractionRing B L]
    (p : ℕ) (l : ℚ) [Fact p.Prime] :
    AfterBaseChange B K L M p l K1 →
      IsExtension.AfterBaseChange B K L M p K1 := sorry
-- Proof strategy: keep the same tensor branch, convert its exact-level witness with
-- `IsAtLevel.OnBranch.toExtension`, and repackage the branch existential.

end AfterBaseChange

/-- Forgetting an exact level on the global base change gives its finite-level owner. -/
@[stacks 09F5 "forgetting the level after global base change"]
theorem OnBaseChange.toExtension
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    {K1 : Type*} [Field K1] [Algebra K K1]
    (h : OnBaseChange B K L M p l K1) :
    IsExtension.OnBaseChange B K L M p K1 := sorry
-- Proof strategy: unpack the global normalization `N`, install its proof-local pins, apply the inner
-- `FiniteLevel.IsAtLevel.toExtension`, retain `N.fractionRing`, and package `N` for the finite-level
-- global owner.

/-- A global exact-level base change has a canonical reduced tensor-product branch view. -/
@[stacks 09F5 "global-to-branch exact finite-level bridge"]
theorem OnBaseChange.toAfterBaseChange
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l : ℚ} [Fact p.Prime]
    {K1 : Type*} [Field K1] [Algebra K K1]
    (h : OnBaseChange B K L M p l K1) :
    AfterBaseChange B K L M p l K1 := sorry
-- Proof strategy: repeat the canonical field-branch construction from
-- `IsExtension.OnBaseChange.toAfterBaseChange`, transporting the exact-level presentation and its
-- rational level across the quotient/tensor equivalences rather than forgetting the level.

/-- The exact level carried by a fixed global base change is unique. -/
@[stacks 09F5 "uniqueness of the level after global base change"]
theorem OnBaseChange.unique
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} {l l' : ℚ} [Fact p.Prime]
    {K1 : Type*} [Field K1] [Algebra K K1]
    (hl : OnBaseChange B K L M p l K1)
    (hl' : OnBaseChange B K L M p l' K1) : l = l' := sorry
-- Proof strategy: unpack both global normalizations, align their proposition-valued field, algebra,
-- DVR, and fraction-ring pins by proof irrelevance, and apply the inner
-- `FiniteLevel.IsAtLevel.unique` on the fixed tensor carriers.

end IsAtLevel

namespace IsExtension

/-- Every global finite-level base change realizes a unique rational level. -/
@[stacks 09F5 "existence of the level after global base change"]
theorem OnBaseChange.exists_level
    {B : Type uB} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
    {M : Type w} [Field M] [Algebra L M]
    {p : ℕ} [Fact p.Prime]
    {K1 : Type*} [Field K1] [Algebra K K1]
    (h : OnBaseChange B K L M p K1) :
    ∃ l : ℚ, IsAtLevel.OnBaseChange B K L M p l K1 := sorry
-- Proof strategy: unpack the global normalization `N`, apply the inner
-- `FiniteLevel.IsExtension.exists_level` under its stored pins, and package the resulting level with
-- the same `N` as an exact-level global base-change witness.

end IsExtension

end FiniteLevel
end KummerArtinSchreier
