/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections.Grading
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen.Power
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module

/-!
# Localized twisted graded sections

This file constructs the degree-zero homogeneous localization of twisted global sections away
from an invertible-module section and its canonical additive comparison with sections on the
section's nonvanishing open.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace GradedSections

/-- The degree-`n` homogeneous submodule of the integer-graded twisted section module, restricted
to nonnegative degrees. -/
abbrev twistedGrading
    (L : X.Modules) [Invertible L] (F : X.Modules) (n : ℕ) :
    Submodule (RingedSpace.globalSectionsRing X.toRingedSpace)
      (RingedSpace.GradedSections.twisted L F) :=
  LinearMap.range <|
    DirectSum.lof (RingedSpace.globalSectionsRing X.toRingedSpace) ℤ
      (fun i ↦ RingedSpace.GradedSections.twistedDegree L F i) (n : ℤ)

/-- Multiplication by a homogeneous section of degree `i` sends a twisted homogeneous section of
degree `j` to degree `i + j`. -/
theorem smul_mem_twistedGrading
    (L : X.Modules) [Invertible L] (F : X.Modules)
    {i j : ℕ} {r : RingedSpace.GradedSections.ring L}
    {m : RingedSpace.GradedSections.twisted L F}
    (hr : r ∈ RingedSpace.GradedSections.grading L i)
    (hm : m ∈ twistedGrading L F j) :
    r • m ∈ twistedGrading L F (i + j) := sorry

/-- The internal grading of the section ring acts compatibly on the nonnegative twisted
homogeneous submodules. -/
noncomputable instance instGradedSMulTwistedGrading
    (L : X.Modules) [Invertible L] (F : X.Modules) :
    SetLike.GradedSMul
      (RingedSpace.GradedSections.grading L)
      (twistedGrading L F) where
  smul_mem := fun i j r m hr hm ↦
    by
      simpa only [vadd_eq_add] using
        smul_mem_twistedGrading L F (i := i) (j := j) (r := r) (m := m) hr hm

/-- A global section of `L`, regarded as a degree-one homogeneous element of its graded section
ring. -/
noncomputable def degreeOne
    (L : X.Modules) [Invertible L] (s : Γ(L, ⊤)) :
    RingedSpace.GradedSections.grading L 1 :=
  DirectSum.InternalGrading.summandEquiv
    (RingedSpace.GradedSections.degree L) 1
    ((RingedSpace.TensorPower.oneIso L).inv.val.app (op ⊤) s)

end GradedSections

/-- The degree-zero homogeneous localization of the twisted graded section module away from a
degree-one section. -/
abbrev localizedTwistedGlobalSections
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) :=
  HomogeneousLocalization.Away.Module.degreeZeroPart
    (RingedSpace.GradedSections.grading L)
    (GradedSections.twistedGrading L F)
    (GradedSections.degreeOne L s)

namespace GradedSections

/-- The standard degree-zero localized fraction `m / s^n`. -/
noncomputable def localizedTwistedMk
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) (m : RingedSpace.GradedSections.twistedDegree L F (n : ℤ)) :
    localizedTwistedGlobalSections L F s :=
  let numerator : twistedGrading L F n :=
    ⟨DirectSum.lof (RingedSpace.globalSectionsRing X.toRingedSpace) ℤ
        (fun i ↦ RingedSpace.GradedSections.twistedDegree L F i) (n : ℤ) m,
      ⟨m, rfl⟩⟩
  let denominatorDegreeNumerator : twistedGrading L F (n • (1 : ℕ)) := by
    simpa using numerator
  ⟨HomogeneousLocalization.Away.Module.powMkHomogeneous
      (RingedSpace.GradedSections.grading L) (twistedGrading L F)
      (degreeOne L s) n denominatorDegreeNumerator,
    HomogeneousLocalization.Away.Module.powMkHomogeneous_mem_degreeZeroPart
      (RingedSpace.GradedSections.grading L) (twistedGrading L F)
      (degreeOne L s) denominatorDegreeNumerator⟩

/-- Every localized twisted section admits a standard homogeneous fraction representative. -/
theorem exists_localizedTwistedMk_eq
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    (z : localizedTwistedGlobalSections L F s) :
    ∃ n : ℕ, ∃ m : RingedSpace.GradedSections.twistedDegree L F (n : ℤ),
      z = localizedTwistedMk L F s n m := sorry

/-- Additive maps out of the localized twisted section module agree when they agree on every
standard homogeneous fraction. -/
theorem localizedTwisted_hom_ext
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    {A : Type v} [AddCommMonoid A]
    {f g : localizedTwistedGlobalSections L F s →+ A}
    (h : ∀ n : ℕ, ∀ m : RingedSpace.GradedSections.twistedDegree L F (n : ℤ),
      f (localizedTwistedMk L F s n m) = g (localizedTwistedMk L F s n m)) :
    f = g := sorry

end GradedSections

/-- Sections of `F` on the nonvanishing open of a global section of an invertible module. -/
abbrev nonvanishingOpenSections
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) :=
  Γ(F, RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
    (RingedSpace.sectionFromTop L s))

namespace GradedSections

/-- The section on the nonvanishing open represented by the homogeneous fraction `m / s^n`:
restrict `m` and contract its tensor-power factor through the canonical trivialization of `L`. -/
noncomputable def localizedTwistedFractionValue
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) (m : RingedSpace.GradedSections.twistedDegree L F (n : ℤ)) :
    nonvanishingOpenSections L F s :=
  let U := RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
    (RingedSpace.sectionFromTop L s)
  SheafOfModules.sectionsOverEquiv F U <|
    SheafOfModules.sectionsMap
      (Invertible.nonvanishingTwistContraction L F s n) <|
      (SheafOfModules.sectionsOverEquiv (F ⊗ (L ^⊗ (n : ℤ))) U).symm
        (((F ⊗ (L ^⊗ (n : ℤ))).val.map
          (homOfLE le_top).op).hom m)

/-- Equal standard localized fractions have equal values after restriction and contraction on the
nonvanishing open. -/
theorem localizedTwistedFractionValue_eq_of_mk_eq
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    {n n' : ℕ}
    {m : RingedSpace.GradedSections.twistedDegree L F (n : ℤ)}
    {m' : RingedSpace.GradedSections.twistedDegree L F (n' : ℤ)}
    (h : localizedTwistedMk L F s n m = localizedTwistedMk L F s n' m') :
    localizedTwistedFractionValue L F s n m =
      localizedTwistedFractionValue L F s n' m' := sorry

/-- The value of a localized twisted section obtained from a standard fraction representative. -/
noncomputable def localizedTwistedComparisonFun
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) :
    localizedTwistedGlobalSections L F s → nonvanishingOpenSections L F s :=
  fun z ↦
    let h := (HomogeneousLocalization.Away.Module.mem_degreeZeroPart_iff
      (RingedSpace.GradedSections.grading L) (twistedGrading L F)
      (degreeOne L s)).mp z.2
    let representative :
        Σ n : ℕ, twistedGrading L F (n • (1 : ℕ)) :=
      ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
    let m : RingedSpace.GradedSections.twistedDegree L F (representative.1 : ℤ) := by
      simpa using Classical.choose representative.2.2
    localizedTwistedFractionValue L F s representative.1 m

/-- The localized comparison function sends zero to zero. -/
theorem localizedTwistedComparisonFun_map_zero
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) :
    localizedTwistedComparisonFun L F s 0 = 0 := sorry

/-- The localized comparison function preserves addition. -/
theorem localizedTwistedComparisonFun_map_add
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    (x y : localizedTwistedGlobalSections L F s) :
    localizedTwistedComparisonFun L F s (x + y) =
      localizedTwistedComparisonFun L F s x +
        localizedTwistedComparisonFun L F s y := sorry

/-- The canonical additive comparison from localized twisted global sections to sections on the
nonvanishing open. -/
noncomputable def localizedTwistedComparison
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) :
    localizedTwistedGlobalSections L F s →+
      nonvanishingOpenSections L F s where
  toFun := localizedTwistedComparisonFun L F s
  map_zero' := localizedTwistedComparisonFun_map_zero L F s
  map_add' := localizedTwistedComparisonFun_map_add L F s

/-- The localized comparison evaluates a standard fraction by restriction and contraction with
the canonical nonvanishing trivialization. -/
theorem localizedTwistedComparison_apply_mk
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) (m : RingedSpace.GradedSections.twistedDegree L F (n : ℤ)) :
    localizedTwistedComparison L F s (localizedTwistedMk L F s n m) =
      localizedTwistedFractionValue L F s n m := sorry

end GradedSections

end AlgebraicGeometry.Scheme.Modules
