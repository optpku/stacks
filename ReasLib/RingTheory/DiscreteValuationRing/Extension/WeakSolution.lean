/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.Smooth.Adic
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Normalization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weak and formal-smooth solutions for DVR extensions

The predicates in this file quantify over the canonical maximal branches of the reduced tensor
product. The branch algebra and its DVR instances are reusable objects, so source-facing Chapter
15 definitions can import this module without owning local notation or local instances.

@stack 09EN
@stack 09EM
-/

open scoped TensorProduct
open IsExtensionOfDiscreteValuationRings
open IsLocalRing
open FieldExtension.TensorProduct

universe u v w x y z

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

namespace DVR.BaseChange.Branch

variable (b : DVR.BaseChange.Branch A B K L K1)

/-- The source normalization localized at a bundled maximal branch. -/
@[stacks 09EM "source normalization branch", stacks 09EN "source branch localization"]
abbrev sourceLocal := Localization.AtPrime b.source.asIdeal

/-- The target normalization localized at a bundled maximal branch. -/
@[stacks 09EM "target normalization branch", stacks 09EN "target branch localization"]
abbrev targetLocal := Localization.AtPrime b.target.asIdeal

/-- The canonical local ring map between the two localizations selected by a branch. -/
@[stacks 09EM "localized base-change branch map"]
noncomputable def localRingHom : b.sourceLocal →+* b.targetLocal :=
  Localization.localRingHom b.source.asIdeal b.target.asIdeal
    (algebraMap (integralClosure A K1)
      (integralClosure B (reduced K L K1)))
    b.liesOver.over

/- Mathlib intentionally keeps `Localization.AtPrime.algebraOfLiesOver` explicit because a global
instance would create localization diamonds.  The same issue occurs for a branch map, so this
canonical structure is a named support owner and is installed only while defining branch predicates. -/
/-- The explicit algebra structure carried by the canonical localized branch map.

This is deliberately a definition rather than a global instance: a tensor-product branch has a
chosen orientation, and registering every such orientation globally would pollute typeclass search.
-/
@[implicit_reducible, stacks 09EM "localized branch algebra support"]
noncomputable def localAlgebra : Algebra b.sourceLocal b.targetLocal :=
  b.localRingHom.toAlgebra

/- The map equality is stated with the named algebra installed only in this theorem. -/
omit [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]
  [IsExtensionOfDiscreteValuationRings A B] [IsFractionRing A K] [IsFractionRing B L] in
/-- The explicit branch algebra has the expected underlying ring homomorphism. -/
@[simp, stacks 09EM "localized branch algebra map"]
theorem localAlgebra_map_eq :
    -- Local instance justification (instance diamond): install the named branch orientation only
    -- while exposing its algebra map.
    letI : Algebra b.sourceLocal b.targetLocal := b.localAlgebra
    algebraMap b.sourceLocal b.targetLocal = b.localRingHom := sorry
-- Proof strategy: unfold `localAlgebra`; `RingHom.toAlgebra` has the original ring homomorphism
-- as its algebra map, so the equality is definitional after the displayed instance pin.

section DVR

variable (d : DVR.BaseChange.Branch A B K L K1)

include d

/- A selected branch is a localization of the reduced tensor-product algebra; the field/DVR
structures below are supplied only after the finite-dimensional hypotheses are present. -/
/- The instances are branch-local support facts, not facts about the unreduced tensor product. -/
/-- A target branch of a finite reduced tensor-product base change is a domain. -/
@[stacks 09EM "target branch domain"]
instance targetIsDomain [FiniteDimensional K K1] : IsDomain d.targetLocal := sorry
-- Proof strategy: apply `integralClosure.BaseChange.targetLocalizationIsDVR` to `d.target` and
-- project the domain witness for its localization.

/-- A source branch of a finite extension of fraction fields is a discrete valuation ring. -/
@[stacks 09EM "source branch DVR"]
instance sourceIsDVR [FiniteDimensional K K1] : IsDiscreteValuationRing d.sourceLocal := sorry
-- Proof strategy: install `integralClosure.BaseChange.sourceIsDedekindDomain`, show the selected
-- maximal ideal is nonzero by contraction to the source DVR maximal ideal, and apply
-- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.

/-- A target branch of a finite reduced tensor-product base change is a discrete valuation ring. -/
@[stacks 09EM "target branch DVR"]
instance targetIsDVR [FiniteDimensional K K1] : IsDiscreteValuationRing d.targetLocal := sorry
-- Proof strategy: apply `integralClosure.BaseChange.targetLocalizationIsDVR` at `d.target` and
-- use its DVR witness after fixing the accompanying domain instance.

/-- A bundled branch of a finite reduced tensor-product base change is an extension of discrete
valuation rings. -/
@[stacks 09EM "localized branch DVR extension"]
theorem localExtension [FiniteDimensional K K1] :
    -- Local instance justification (instance diamond): the extension theorem is stated for the
    -- explicit branch algebra without registering that orientation globally.
    letI : Algebra d.sourceLocal d.targetLocal := d.localAlgebra
    IsExtensionOfDiscreteValuationRings d.sourceLocal d.targetLocal := sorry
-- Proof strategy: construct `IsExtensionOfDiscreteValuationRings` from
-- `Localization.isLocalHom_localRingHom` and injectivity of localization at the prime target;
-- rewrite the algebra map with `localAlgebra_map_eq`.

end DVR

/-- The weakly unramified property of one localized base-change branch, owned by the bundled
branch namespace so downstream statements can use `b.IsWeakSolution`. -/
@[stacks 09EN "weakly unramified localized branch"]
def IsWeakSolution [FiniteDimensional K K1]
    (b : DVR.BaseChange.Branch A B K L K1) : Prop :=
  -- Local instance justification (instance diamond): install the named oriented branch algebra
  -- only while interpreting `WeaklyUnramified`.
  letI : Algebra b.sourceLocal b.targetLocal := b.localAlgebra
  -- Local instance justification (proof-local temporary data): the DVR extension theorem supplies
  -- the class required by `WeaklyUnramified` for this branch only.
  letI : IsExtensionOfDiscreteValuationRings b.sourceLocal b.targetLocal :=
    b.localExtension
  WeaklyUnramified b.sourceLocal b.targetLocal

/-- The formal-smoothness property of one localized base-change branch, owned by the bundled branch
namespace so it can be addressed as `b.IsSolution`. -/
@[stacks 09EN "formally smooth localized branch"]
def IsSolution [FiniteDimensional K K1]
    (b : DVR.BaseChange.Branch A B K L K1) : Prop :=
  -- Local instance justification (defeq pin): keep the ideal in the same canonical `CommRing`
  -- model used by the localized branch map.
  letI : CommRing b.targetLocal := OreLocalization.instCommRing
  b.localRingHom.formally_smooth_for_adic (maximalIdeal b.targetLocal)

end DVR.BaseChange.Branch

end

section SourcePredicates

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Algebra A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

variable (A) (B) (K) (L) (K1) in
/-- Definition 15.116.1 (1): K1 / K is a weak solution when every maximal localized branch is
weakly unramified. -/
@[stacks 09EN "weak solution for a DVR extension"]
def IsWeakSolutionFor
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K K1] : Prop :=
  ∀ (p : Ideal (integralClosure A K1)) [p.IsMaximal]
    (q : Ideal (integralClosure B (reduced K L K1)))
    [q.IsMaximal] [q.LiesOver p],
    DVR.BaseChange.Branch.IsWeakSolution (DVR.BaseChange.Branch.ofIdeals (K := K) (L := L) p q)

variable (A) (B) (K) (L) (K1) in
/-- Definition 15.116.1 (2): K1 / K is a solution when every localized branch is formally smooth
for the target maximal-ideal topology. -/
@[stacks 09EN "formal-smooth solution for a DVR extension"]
def IsSolutionFor
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K K1] : Prop :=
  ∀ (p : Ideal (integralClosure A K1)) [p.IsMaximal]
    (q : Ideal (integralClosure B (reduced K L K1)))
    [q.IsMaximal] [q.LiesOver p],
    DVR.BaseChange.Branch.IsSolution (DVR.BaseChange.Branch.ofIdeals (K := K) (L := L) p q)

variable (A) (B) (K) (L) (K1) in
/-- Definition 15.116.1 (3): a separable solution is a formal-smooth solution together with
separability of K1 / K. -/
@[stacks 09EN "separable solution for a DVR extension"]
def IsSeparableSolutionFor
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsDomain B] [IsDiscreteValuationRing B]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K K1] : Prop :=
  IsSolutionFor A B K L K1 ∧ Algebra.IsSeparable K K1

end SourcePredicates

namespace DVR.BaseChange

section FactorPredicates

variable {B : Type v} {C : Type w} {K : Type u} {L : Type x} {M : Type y} {K1 : Type z}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra B C] [IsExtensionOfDiscreteValuationRings B C]
variable [Field K] [Field L] [Algebra K L]
variable [Field M] [Algebra B L] [Algebra B M] [Algebra C M] [Algebra L M]
variable [IsFractionRing B L] [IsFractionRing C M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field K1] [Algebra K K1] [FiniteDimensional K K1]

/-- Lemma 15.116.4: the weak-solution condition on the canonical quotient field of a reduced
tensor-product factor.  The quotient carrier is kept source-faithful; its canonical branch
instances are installed only inside this reusable predicate. -/
@[stacks 09ES "weak solution on a reduced tensor-product factor"]
def IsWeakSolutionOnFactor
    (m : MaximalSpectrum (reduced K L K1)) : Prop :=
  let F := reduced K L K1 ⧸ m.asIdeal
  -- Local instance justification (defeq pin): choose the quotient field structure attached to the
  -- selected maximal ideal while interpreting the source predicate.
  let _ : Field F := Ideal.Quotient.field m.asIdeal
  IsWeakSolutionFor B C L M F

/-- Lemma 15.116.4: the formal-smooth solution condition on a canonical reduced tensor-product
factor, with the same source-faithful quotient carrier as `IsWeakSolutionOnFactor`. -/
@[stacks 09ES "solution on a reduced tensor-product factor"]
def IsSolutionOnFactor
    (m : MaximalSpectrum (reduced K L K1)) : Prop :=
  let F := reduced K L K1 ⧸ m.asIdeal
  -- Local instance justification (defeq pin): choose the quotient field structure attached to the
  -- selected maximal ideal while interpreting the source predicate.
  let _ : Field F := Ideal.Quotient.field m.asIdeal
  IsSolutionFor B C L M F

end FactorPredicates

end DVR.BaseChange

section SourceSpecifications

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

namespace IsWeakSolutionFor

variable (A) (B) (K) (L) (K1)

/-- The branchwise form of the weak-solution predicate. -/
@[stacks 09EN "weak solution branch specification"]
theorem branch_spec [FiniteDimensional K K1] (h : IsWeakSolutionFor A B K L K1)
    (b : DVR.BaseChange.Branch A B K L K1) :
    b.IsWeakSolution := sorry
-- Proof strategy: apply `h` to `b.source` and `b.target`, then identify the reconstructed
-- `Branch.ofIdeals` with `b` using `DVR.BaseChange.Branch.ext`.

/-- The textbook quantification over pairs of maximal ideals is equivalent to quantifying over
bundled base-change branches. -/
@[stacks 09EN "weak solution ideal-pair specification"]
theorem iff_forall_ideals [FiniteDimensional K K1] :
    IsWeakSolutionFor A B K L K1 ↔
      ∀ (p : Ideal (integralClosure A K1)) [p.IsMaximal]
        (q : Ideal (integralClosure B (reduced K L K1)))
        [q.IsMaximal] [q.LiesOver p],
        (DVR.BaseChange.Branch.ofIdeals (K := K) (L := L) p q).IsWeakSolution := sorry
-- Proof strategy: unfold `IsWeakSolutionFor`; the right-hand side is its defining ideal-pair
-- quantification, with only namespace projections normalized.

/-- Maximal-ideal form of the weak-solution condition. -/
@[stacks 09EN "weak solution maximal-ideal criterion"]
theorem iff_map_maximalIdeal [FiniteDimensional K K1] :
    IsWeakSolutionFor A B K L K1 ↔
      ∀ (p : Ideal (integralClosure A K1)) [p.IsMaximal]
        (q : Ideal (integralClosure B (reduced K L K1)))
        [q.IsMaximal] [q.LiesOver p],
        let b := DVR.BaseChange.Branch.ofIdeals (K := K) (L := L) p q
        Ideal.map b.localRingHom (maximalIdeal b.sourceLocal) =
          maximalIdeal b.targetLocal := sorry
-- Proof strategy: rewrite with `iff_forall_ideals`, unfold `Branch.IsWeakSolution`, install the
-- named `localAlgebra` and `localExtension`, then apply
-- `IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal` and
-- `Branch.localAlgebra_map_eq`.

/-- Bundled-branch form of the maximal-ideal criterion. -/
@[stacks 09EN "weak solution maximal-ideal criterion on branches"]
theorem iff_map_maximalIdeal_on_branch [FiniteDimensional K K1] :
    IsWeakSolutionFor A B K L K1 ↔
      ∀ b : DVR.BaseChange.Branch A B K L K1,
        Ideal.map b.localRingHom (maximalIdeal b.sourceLocal) =
          maximalIdeal b.targetLocal := sorry
-- Proof strategy: use `iff_map_maximalIdeal` in one direction; for the converse specialize the
-- branch quantifier to `Branch.ofIdeals`, while `Branch.ext` identifies every bundled branch with
-- the one reconstructed from its source and target ideals.

end IsWeakSolutionFor

namespace IsSolutionFor

variable (A) (B) (K) (L) (K1)

/-- The branchwise form of the formal-smooth solution predicate. -/
@[stacks 09EN "formal-smooth solution branch specification"]
theorem branch_spec [FiniteDimensional K K1] (h : IsSolutionFor A B K L K1)
    (b : DVR.BaseChange.Branch A B K L K1) :
    b.IsSolution := sorry
-- Proof strategy: specialize `h` to `b.source` and `b.target`, and rewrite the reconstructed
-- ideal-pair branch to `b` with `DVR.BaseChange.Branch.ext`.

/-- The formal-smooth solution predicate in the textbook's unbundled ideal-pair form. -/
@[stacks 09EN "formal-smooth solution ideal-pair specification"]
theorem iff_forall_ideals [FiniteDimensional K K1] :
    IsSolutionFor A B K L K1 ↔
      ∀ (p : Ideal (integralClosure A K1)) [p.IsMaximal]
        (q : Ideal (integralClosure B (reduced K L K1)))
        [q.IsMaximal] [q.LiesOver p],
        (DVR.BaseChange.Branch.ofIdeals (K := K) (L := L) p q).IsSolution := sorry
-- Proof strategy: unfold `IsSolutionFor`; its definition is exactly the displayed quantification
-- over maximal ideal pairs and the canonical `Branch.ofIdeals` formal-smoothness predicate.

end IsSolutionFor
