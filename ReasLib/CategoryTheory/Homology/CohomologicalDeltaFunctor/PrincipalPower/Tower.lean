/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.ModuleCat
public import ReasLib.CategoryTheory.Linear.PrincipalPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal-power towers for cohomological delta functors

Let `H` be a cohomological delta functor from an `R`-linear abelian category to `R`-modules.
When every degree functor is `R`-linear, the canonical short exact rows for powers of a scalar
assemble into a short exact sequence of quotient, cohomology, and torsion towers.  This leaf owns
that construction without mentioning schemes, global sections, or a chosen derived model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
variable (H : CohomologicalDeltaFunctor C (ModuleCat.{w} R))
variable [∀ p : ℕ, Functor.Linear R (H.F p).obj]

/-- The degree-`p` cohomology tower of the positive principal-power quotient system of `M`. -/
@[stacks 0H3A "principal-power quotient cohomology tower"]
abbrev quotientSystem (f : R) (M : C) (p : ℕ) :
    SequentialInverseSystem (ModuleCat.{w} R) :=
  CategoryTheory.Linear.PrincipalPower.quotientSystem f M ⋙ (H.F p).obj

/-- The degree-`p+1` principal-power torsion tower of `H(M)`. -/
@[stacks 0H3A "principal-power cohomology torsion tower"]
abbrev torsionSystem (f : R) (M : C) (p : ℕ) :
    SequentialInverseSystem (ModuleCat.{w} R) :=
  CategoryTheory.Linear.PrincipalPower.kernelSystem f (((H.F (p + 1)).obj).obj M)

/-- The canonical map from `H^p(M)` to the cohomology of the `n`th quotient stage. -/
@[stacks 0H3A "cohomology quotient-stage map"]
abbrev toQuotientStage (f : R) (M : C) (p n : ℕ) :
    ((H.F p).obj).obj M ⟶ (quotientSystem H f M p).obj (op n) :=
  (H.F p).obj.map
    (cokernel.π
      (CategoryTheory.Linear.PrincipalPower.smulPow f M (n + 1)))

/-- Linearity identifies the image of a principal-power scalar with scalar multiplication in the
target module category. -/
@[stacks 0H3A "linear cohomology scalar-power formula"]
theorem map_smulPow (f : R) (M : C) (p n : ℕ) :
    (H.F p).obj.map (CategoryTheory.Linear.PrincipalPower.smulPow f M n) =
      (f ^ n) • 𝟙 (((H.F p).obj).obj M) := sorry

/-- The cohomology map to a quotient stage kills the corresponding scalar power. -/
theorem toQuotientStage_zero (f : R) (M : C) (p n : ℕ) :
    CategoryTheory.Linear.PrincipalPower.smulPow f (((H.F p).obj).obj M) (n + 1) ≫
        toQuotientStage H f M p n = 0 := sorry

/-- The quotient-stage map descended from `toQuotientStage`. -/
noncomputable abbrev quotientMapApp (f : R) (M : C) (p n : ℕ) :
    CategoryTheory.Linear.PrincipalPower.quotientStage f (((H.F p).obj).obj M) n ⟶
      (quotientSystem H f M p).obj (op n) :=
  cokernel.desc
    (CategoryTheory.Linear.PrincipalPower.smulPow f (((H.F p).obj).obj M) (n + 1))
    (toQuotientStage H f M p n)
    (toQuotientStage_zero H f M p n)

/-- The quotient-stage maps commute with the two quotient towers. -/
theorem quotientMapApp_naturality (f : R) (M : C) (p n : ℕ) :
    (CategoryTheory.Linear.PrincipalPower.quotientSystem f (((H.F p).obj).obj M)).stepMap n ≫
        quotientMapApp H f M p n =
      quotientMapApp H f M p (n + 1) ≫
        (quotientSystem H f M p).stepMap n := sorry

/-- The natural transformation from the quotient tower of `H^p(M)` to the cohomology quotient
tower. -/
@[stacks 0H3A "cohomology quotient tower comparison"]
noncomputable def quotientMap (f : R) (M : C) (p : ℕ) :
    CategoryTheory.Linear.PrincipalPower.quotientSystem f (((H.F p).obj).obj M) ⟶
      quotientSystem H f M p :=
  NatTrans.ofOpSequence
    (quotientMapApp H f M p)
    (quotientMapApp_naturality H f M p)

/-- The cohomological boundary map lands in the corresponding categorical power-kernel stage. -/
theorem boundaryMapApp_zero (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p n : ℕ) :
    H.δ (CategoryTheory.Linear.PrincipalPower.row_shortExact f M n) p ≫
        CategoryTheory.Linear.PrincipalPower.smulPow f (((H.F (p + 1)).obj).obj M) (n + 1) = 0 := sorry

/-- The stagewise boundary map from quotient cohomology to the next-degree power-kernel stage. -/
@[stacks 0H3A "cohomology boundary stage map"]
noncomputable abbrev boundaryMapApp (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p n : ℕ) :
    (quotientSystem H f M p).obj (op n) ⟶
      (torsionSystem H f M p).obj (op n) :=
  kernel.lift
    (CategoryTheory.Linear.PrincipalPower.smulPow f (((H.F (p + 1)).obj).obj M) (n + 1))
    (H.δ (CategoryTheory.Linear.PrincipalPower.row_shortExact f M n) p)
    (boundaryMapApp_zero H f M p n)

/-- The stagewise boundary maps commute with the quotient and torsion transitions. -/
theorem boundaryMapApp_naturality (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p n : ℕ) :
    (quotientSystem H f M p).stepMap n ≫ boundaryMapApp H f M p n =
      boundaryMapApp H f M p (n + 1) ≫
        (torsionSystem H f M p).stepMap n := sorry

/-- The natural transformation of quotient cohomology to principal-power torsion towers. -/
@[stacks 0H3A "cohomology boundary tower map"]
noncomputable def boundaryMap (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    quotientSystem H f M p ⟶ torsionSystem H f M p :=
  NatTrans.ofOpSequence
    (boundaryMapApp H f M p)
    (boundaryMapApp_naturality H f M p)

/-- The quotient comparison followed by the cohomological boundary map is zero. -/
theorem quotientMap_comp_boundaryMap_zero (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    quotientMap H f M p ≫ boundaryMap H f M p = 0 := sorry

/-- The canonical short complex of principal-power cohomology towers. -/
@[stacks 0H3A "principal-power cohomology tower short complex"]
noncomputable def shortComplex (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    ShortComplex (SequentialInverseSystem (ModuleCat.{w} R)) :=
  ShortComplex.mk
    (quotientMap H f M p)
    (boundaryMap H f M p)
    (quotientMap_comp_boundaryMap_zero H f M p)

/-- The left term of the principal-power cohomology short complex. -/
@[simp, stacks 0H3A "left principal-power cohomology tower"]
theorem shortComplex_X₁ (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (shortComplex H f M p).X₁ =
      CategoryTheory.Linear.PrincipalPower.quotientSystem f (((H.F p).obj).obj M) := sorry

/-- The middle term of the principal-power cohomology short complex. -/
@[simp, stacks 0H3A "middle principal-power cohomology tower"]
theorem shortComplex_X₂ (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (shortComplex H f M p).X₂ = quotientSystem H f M p := sorry

/-- The right term of the principal-power cohomology short complex. -/
@[simp, stacks 0H3A "right principal-power cohomology tower"]
theorem shortComplex_X₃ (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (shortComplex H f M p).X₃ = torsionSystem H f M p := sorry

/-- The left map of the principal-power cohomology short complex. -/
@[simp, stacks 0H3A "principal-power quotient comparison in the short complex"]
theorem shortComplex_f (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (shortComplex H f M p).f = quotientMap H f M p := sorry

/-- The right map of the principal-power cohomology short complex. -/
@[simp, stacks 0H3A "principal-power boundary map in the short complex"]
theorem shortComplex_g (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (shortComplex H f M p).g = boundaryMap H f M p := sorry

/-- The principal-power cohomology tower short complex is short exact. -/
@[stacks 0H3A "short exact principal-power cohomology towers"]
theorem shortComplex_shortExact (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (shortComplex H f M p).ShortExact := sorry

/-- The inverse-limit short complex attached to the principal-power cohomology towers. -/
@[stacks 0H3A "principal-power cohomology completion short complex"]
noncomputable abbrev completionShortComplex (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    ShortComplex (ModuleCat.{w} R) :=
  (shortComplex H f M p).map lim

/-- The left term of the inverse-limit principal-power cohomology short complex. -/
@[simp, stacks 0H3A "left term of the principal-power cohomology completion"]
theorem completionShortComplex_X₁ (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (completionShortComplex H f M p).X₁ =
      limit (CategoryTheory.Linear.PrincipalPower.quotientSystem f (((H.F p).obj).obj M)) := sorry

/-- The middle term of the inverse-limit principal-power cohomology short complex. -/
@[simp, stacks 0H3A "middle term of the principal-power cohomology completion"]
theorem completionShortComplex_X₂ (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (completionShortComplex H f M p).X₂ = limit (quotientSystem H f M p) := sorry

/-- The right term of the inverse-limit principal-power cohomology short complex. -/
@[simp, stacks 0H3A "right term of the principal-power cohomology completion"]
theorem completionShortComplex_X₃ (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (completionShortComplex H f M p).X₃ =
      CategoryTheory.Linear.PrincipalPower.tateObject f (((H.F (p + 1)).obj).obj M) := sorry

/-- The inverse-limit row is short exact because the quotient tower is Mittag-Leffler. -/
@[stacks 0H3A "short exact principal-power cohomology completion"]
theorem completionShortComplex_shortExact (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (completionShortComplex H f M p).ShortExact := sorry

/-- The concrete isomorphism on first derived inverse limits, the instance of the Milnor
comparison `ModuleCat.ShortExact.firstDerivedLimitIso` for the short exact principal-power row
whose left term, a principal-power quotient tower, is Mittag-Leffler. -/
@[stacks 0H3A "principal-power cohomology first derived limit iso"]
noncomputable def firstDerivedLimitIso (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (quotientSystem H f M p).firstDerivedLimit ≅
      (torsionSystem H f M p).firstDerivedLimit :=
  CategoryTheory.ModuleCat.ShortExact.firstDerivedLimitIso
    (R := R) (S := shortComplex H f M p)
    (shortComplex_shortExact H f M p)
    (CategoryTheory.Linear.PrincipalPower.quotientSystem_isMittagLeffler f
      (((H.F p).obj).obj M))

/-- The canonical map on first derived inverse limits is an isomorphism. -/
@[stacks 0H3A "principal-power cohomology first derived limit isomorphism"]
theorem firstDerivedLimitMap_isIso (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    IsIso (SequentialInverseSystem.firstDerivedLimitMap (boundaryMap H f M p)) :=
  (firstDerivedLimitIso H f M p).isIso_hom

/-- The quotient cohomology and torsion towers are Mittag-Leffler simultaneously. -/
@[stacks 0H3A "principal-power cohomology Mittag-Leffler equivalence"]
theorem isMittagLeffler_iff_torsion (f : R) (M : C)
    [CategoryTheory.Linear.PrincipalPower.IsTorsionFree f M] (p : ℕ) :
    (quotientSystem H f M p).IsMittagLeffler ↔
      (torsionSystem H f M p).IsMittagLeffler := sorry

end CategoryTheory.CohomologicalDeltaFunctor.PrincipalPower
