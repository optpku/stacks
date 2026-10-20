/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Relations between precoverage presentations

This leaf isolates the generic mechanism behind comparisons of precoverages:
if a relation on fixed-target families preserves their generated sieves, then
replacement of covers along that relation preserves the generated topology and
the corresponding set-valued sheaf condition.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Precoverage

open SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C]

/-- A relation between fixed-target families, uniform in the target object. -/
abbrev FamilyRelation (C : Type u) [Category.{v} C] :=
  ∀ {X : C}, SemiRepresentableFamily.Over.{max u v} X →
    SemiRepresentableFamily.Over.{max u v} X → Prop

/-- A family relation preserves generated sieves when related families define
the same sieve on their common target. -/
def FamilyRelation.preservesSieve (R : FamilyRelation C) : Prop :=
  ∀ {X : C} {𝒰 𝒱 : SemiRepresentableFamily.Over.{max u v} X},
    R 𝒰 𝒱 → 𝒰.toSieve = 𝒱.toSieve

/-- Every `K`-cover can be replaced by an `L`-cover related to it by `R`. -/
def coversUpTo (K L : Precoverage C) (R : FamilyRelation C) : Prop :=
  ∀ {X : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} X),
    IsCovering K 𝒰 →
      ∃ 𝒱 : SemiRepresentableFamily.Over.{max u v} X,
        IsCovering L 𝒱 ∧ R 𝒰 𝒱

/-- Replacement of covering families along a sieve-preserving relation induces
an inclusion of the generated Grothendieck topologies. -/
theorem toGrothendieck_le_of_coversUpTo
    {K L : Precoverage C} {R : FamilyRelation C}
    (hR : R.preservesSieve) (hKL : K.coversUpTo L R) :
    K.toGrothendieck ≤ L.toGrothendieck := sorry

/-- A set-valued sheaf for `L` is a sheaf for `K` after replacement of
`K`-covers by `L`-covers along a sieve-preserving relation. -/
theorem isSheaf_of_coversUpTo
    {K L : Precoverage C} {R : FamilyRelation C} {P : Cᵒᵖ ⥤ Type w}
    (hR : R.preservesSieve) (hKL : K.coversUpTo L R)
    (hP : Presheaf.IsSheaf L.toGrothendieck P) :
    Presheaf.IsSheaf K.toGrothendieck P := sorry

/-- Mutual cover replacement along a sieve-preserving relation gives
equivalent set-valued sheaf conditions. -/
theorem isSheaf_iff_of_mutual_coversUpTo
    {K L : Precoverage C} {R : FamilyRelation C} {P : Cᵒᵖ ⥤ Type w}
    (hR : R.preservesSieve)
    (hKL : K.coversUpTo L R) (hLK : L.coversUpTo K R) :
    Presheaf.IsSheaf K.toGrothendieck P ↔
      Presheaf.IsSheaf L.toGrothendieck P := sorry

/-- An enlargement whose covers are replaceable by covers from the smaller
precoverage along a sieve-preserving relation generates the same topology. -/
theorem toGrothendieck_eq_of_le_of_coversUpTo
    {K L : Precoverage C} {R : FamilyRelation C}
    (hR : R.preservesSieve) (hKL : K ≤ L) (hLK : L.coversUpTo K R) :
    L.toGrothendieck = K.toGrothendieck := sorry

/-- Two sub-precoverages of one ambient precoverage generate the same topology
when its covers can be replaced by covers from either sub-precoverage along a
sieve-preserving relation. -/
theorem toGrothendieck_eq_of_common_ambient_coversUpTo
    {K K₁ K₂ : Precoverage C} {R : FamilyRelation C}
    (hR : R.preservesSieve) (h₁ : K₁ ≤ K) (h₂ : K₂ ≤ K)
    (hK₁ : K.coversUpTo K₁ R) (hK₂ : K.coversUpTo K₂ R) :
    K₁.toGrothendieck = K₂.toGrothendieck := sorry

/-- Under common ambient replacement along a sieve-preserving relation, a
set-valued presheaf is a sheaf for either sub-precoverage exactly together. -/
theorem isSheaf_iff_of_common_ambient_coversUpTo
    {K K₁ K₂ : Precoverage C} {R : FamilyRelation C} {P : Cᵒᵖ ⥤ Type w}
    (hR : R.preservesSieve) (h₁ : K₁ ≤ K) (h₂ : K₂ ≤ K)
    (hK₁ : K.coversUpTo K₁ R) (hK₂ : K.coversUpTo K₂ R) :
    Presheaf.IsSheaf K₁.toGrothendieck P ↔
      Presheaf.IsSheaf K₂.toGrothendieck P := sorry

end CategoryTheory.Precoverage
