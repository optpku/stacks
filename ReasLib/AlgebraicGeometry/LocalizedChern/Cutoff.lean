/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass BivariantClass.Cutoff

/-- The mixed cutoff Chern series whose degrees below `p` are ambient and whose
degrees at least `p` are relative localized classes. -/
def cutoffChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ)) :
    Cutoff δ i p (n : ℤ) :=
  if h : (n : ℤ) < p then ofAmbient δ i h ambient else ofRelative δ i h localized

/-- Below the cutoff, `cutoffChernClass` recovers the ambient class. -/
theorem cutoffChernClass_apply_lt
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ))
    (h : (n : ℤ) < p) :
    toAmbient δ i h (cutoffChernClass δ i p n ambient localized) = ambient := sorry

/-- At or above the cutoff, `cutoffChernClass` recovers the relative localized class. -/
theorem cutoffChernClass_apply_ge
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ))
    (h : ¬(n : ℤ) < p) :
    toRelative δ i h (cutoffChernClass δ i p n ambient localized) = localized := sorry

end AlgebraicGeometry.LocalizedChern
