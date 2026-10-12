/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Derived
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Injective

@[expose] public section

/-!
# Derived Limits from Injective Lower-Truncation Towers

This leaf relates an injective lower-truncation resolution to the derived
lower-truncation tower.  All derived-localization assumptions are explicit;
the propositions here do not choose an inverse limit or a Milnor triangle.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite

noncomputable section

universe w u v

namespace CochainComplex.LowerTruncation.Resolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 070M: the derived image of every stage-comparison map in an injective
lower-truncation resolution is an isomorphism. -/
@[stacks 070M]
instance Comparison.isIso {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncation.Resolution (isInjective 𝒜) K) (n : ℕ) :
    IsIso (DerivedCategory.Q.map (S.comparison.app (op n))) := sorry

/-- Stacks 070M: the canonical map from a complex to the inverse limit of its injective
lower-truncation resolution is a compatible derived-limit comparison. -/
@[stacks 070M]
theorem Comparison.intoLimit {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜] (S : LowerTruncation.Resolution (isInjective 𝒜) K) :
    LowerTruncation.Comparison.Exists K (DerivedCategory.Q.map S.intoLimit) := sorry

/-- Stacks 070Q: any map into the inverse limit whose composites with the projections are the
stage maps of an injective lower-truncation resolution has the canonical derived comparison
property.  This is the reusable bridge for source-facing compatible-map formulations. -/
@[stacks 070Q]
theorem Comparison.exists_of_comp_π {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜]
    (S : LowerTruncation.Resolution (isInjective 𝒜) K)
    (γ : K ⟶ limit S.tower)
    (hγ : ∀ n : ℕ, γ ≫ limit.π S.tower (op n) = S.fromSource n) :
    LowerTruncation.Comparison.Exists K (DerivedCategory.Q.map γ) := sorry

/-- Stacks 070M: the inverse limit of an injective lower-truncation resolution is a homotopy
limit of the canonical derived lower-truncation tower. -/
@[stacks 070M]
theorem Comparison.limit {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜] (S : LowerTruncation.Resolution (isInjective 𝒜) K) :
    HomotopyLimit.IsOf (LowerTruncation.derivedTower K)
      (DerivedCategory.Q.obj (limit S.tower)) := sorry

/-- Stacks 070M: the canonical map to the inverse limit is a quasi-isomorphism exactly when any
compatible comparison to the derived lower-truncation limit is an isomorphism. -/
@[stacks 070M]
theorem Comparison.quasiIso_iff {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜] (S : LowerTruncation.Resolution (isInjective 𝒜) K)
    {L : DerivedCategory 𝒜} {c : DerivedCategory.Q.obj K ⟶ L}
    (hc : LowerTruncation.Comparison.Exists K c) :
    QuasiIso S.intoLimit ↔ IsIso c := sorry

end CochainComplex.LowerTruncation.Resolution
