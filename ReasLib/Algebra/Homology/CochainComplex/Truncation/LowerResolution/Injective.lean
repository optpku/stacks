/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.SequentialLimit
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution

@[expose] public section

/-!
# Injective Lower-Truncation Resolution Towers

This leaf specializes lower-truncation resolution towers to injective terms.
It provides their canonical countable limits and the K-injectivity facts
needed by derived-category applications, without selecting a derived
localization.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite

noncomputable section

universe u v

namespace CochainComplex.LowerTruncation.Resolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 070M: every degreewise inverse system underlying an injective lower-truncation
resolution has a limit. -/
@[stacks 070M]
noncomputable instance hasLimit_eval {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜] (S : LowerTruncation.Resolution (isInjective 𝒜) K) (i : ℤ) :
    HasLimit (S.tower ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) := sorry

/-- Stacks 070M: an injective lower-truncation resolution has an inverse limit in cochain
complexes. -/
@[stacks 070M]
noncomputable instance hasLimit {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜] (S : LowerTruncation.Resolution (isInjective 𝒜) K) :
    HasLimit S.tower := sorry

/-- Stacks 070M: every stage of an injective lower-truncation resolution is canonically
K-injective. -/
@[stacks 070M]
instance stage_isKInjective {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncation.Resolution (isInjective 𝒜) K) (n : ℕ) :
    (S.stage n).IsKInjective := sorry

/-- Stacks 070M: the inverse limit of an injective lower-truncation resolution is canonically
K-injective. -/
@[stacks 070M]
noncomputable instance limit_isKInjective {K : CochainComplex 𝒜 ℤ}
    [HasCountableProducts 𝒜] (S : LowerTruncation.Resolution (isInjective 𝒜) K) :
    (limit S.tower).IsKInjective := sorry

end CochainComplex.LowerTruncation.Resolution
