/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded finite locally free complexes of module sheaves

This leaf packages the two termwise conditions used for local models of perfect complexes as
`ObjectProperty` values.  The generic `CochainComplex.boundedTermsIn` construction remains the
owner of the bounded-termwise pattern.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {R : Sheaf J RingCat.{w}}

/-- Lemma 20.49.3 (2), reusable owner: bounded complexes whose terms are finite locally free. -/
@[stacks 0BCJ "bounded finite locally free"]
def boundedFiniteLocallyFree :
    ObjectProperty (_root_.CochainComplex (SheafOfModules.{w} R) ℤ) :=
  _root_.CochainComplex.boundedTermsIn
    (fun M : SheafOfModules.{w} R ↦ IsFiniteLocallyFree M)

/-- A complex of module sheaves is bounded finite locally free when it belongs to
`boundedFiniteLocallyFree`. -/
abbrev IsBoundedFiniteLocallyFree
    (K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) : Prop :=
  boundedFiniteLocallyFree K

/-- Bounded finite locally free complexes, as a full subcategory. -/
abbrev BoundedFiniteLocallyFree :=
  (boundedFiniteLocallyFree (R := R)).FullSubcategory

/-- Membership in `boundedFiniteLocallyFree` is boundedness together with finite local freeness
in every degree. -/
theorem mem_boundedFiniteLocallyFree_iff
    (K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    boundedFiniteLocallyFree K ↔
      _root_.CochainComplex.bounded (SheafOfModules.{w} R) K ∧
        ∀ i : ℤ, IsFiniteLocallyFree (K.X i) := sorry

/-- Bounded finite local freeness can be expressed using explicit lower and upper bounds. -/
theorem isBoundedFiniteLocallyFree_iff
    (K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    IsBoundedFiniteLocallyFree K ↔
      (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
        ∀ i : ℤ, IsFiniteLocallyFree (K.X i) := sorry

/-- Lemma 20.49.3 (3), reusable owner: bounded complexes whose terms are finite free. -/
@[stacks 0BCJ "bounded finite free"]
def boundedFiniteFree :
    ObjectProperty (_root_.CochainComplex (SheafOfModules.{w} R) ℤ) :=
  _root_.CochainComplex.boundedTermsIn
    (fun M : SheafOfModules.{w} R ↦ IsFiniteFree M)

/-- A complex of module sheaves is bounded finite free when it belongs to
`boundedFiniteFree`. -/
abbrev IsBoundedFiniteFree
    (K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) : Prop :=
  boundedFiniteFree K

/-- Bounded finite free complexes, as a full subcategory. -/
abbrev BoundedFiniteFree :=
  (boundedFiniteFree (R := R)).FullSubcategory

/-- Membership in `boundedFiniteFree` is boundedness together with finite freeness in every
degree. -/
theorem mem_boundedFiniteFree_iff
    (K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    boundedFiniteFree K ↔
      _root_.CochainComplex.bounded (SheafOfModules.{w} R) K ∧
        ∀ i : ℤ, IsFiniteFree (K.X i) := sorry

/-- Bounded finite freeness can be expressed using explicit lower and upper bounds. -/
theorem isBoundedFiniteFree_iff
    (K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    IsBoundedFiniteFree K ↔
      (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
        ∀ i : ℤ, IsFiniteFree (K.X i) := sorry

/-- Bounded finite free complexes are bounded finite locally free. -/
theorem boundedFiniteFree_le_boundedFiniteLocallyFree :
    boundedFiniteFree (R := R) ≤ boundedFiniteLocallyFree (R := R) := sorry

/-- A bounded finite free complex is bounded finite locally free. -/
theorem IsBoundedFiniteFree.isBoundedFiniteLocallyFree
    {K : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hK : IsBoundedFiniteFree K) : IsBoundedFiniteLocallyFree K := sorry

end SheafOfModules.CochainComplex
