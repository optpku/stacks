/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}}

/-- The inverse system whose stage `n` is the global sections of `M / I ^ (n + 1) M`. -/
noncomputable def positiveSectionsSystem (I : X.IdealSheafData) (M : X.Modules) :
    SequentialInverseSystem (Type u) :=
  SequentialInverseSystem.shift
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.sectionsSystem.{u, u, u}
      I.toSubobject M) 1

/-- Stage `n` of `positiveSectionsSystem I M` is the global sections of
`M / I ^ (n + 1) M`. -/
theorem positiveSectionsSystem_obj (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (positiveSectionsSystem I M).obj (op n) =
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        I.toSubobject M (n + 1)).sections := sorry

/-- The map from global sections of `M` to the sections of its positive stage `n`. -/
noncomputable def sectionsProjection (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj M.sections).obj (op n) ⟶
      (positiveSectionsSystem I M).obj (op n) :=
  ↾(SheafOfModules.sectionsMap
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.projection.{u, u, u}
      I.toSubobject M (1 + n)))

/-- The global-section projections commute with the transitions in the positive
ideal-power system. -/
theorem sectionsProjection_naturality (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj M.sections).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ sectionsProjection I M n =
      sectionsProjection I M (n + 1) ≫
        (positiveSectionsSystem I M).map
          (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from the global sections of `M` to the positive ideal-power
section system. -/
noncomputable def sectionsCone (I : X.IdealSheafData) (M : X.Modules) :
    Cone (positiveSectionsSystem I M) where
  pt := M.sections
  π := NatTrans.ofOpSequence (sectionsProjection I M)
    (sectionsProjection_naturality I M)

/-- The canonical map from global sections to the inverse limit of the positive ideal-power
section system. -/
noncomputable def sectionsComparison (I : X.IdealSheafData) (M : X.Modules) :
    M.sections → limit (positiveSectionsSystem I M) :=
  limit.lift (positiveSectionsSystem I M) (sectionsCone I M)

/-- Every limit projection of `sectionsComparison I M` is the corresponding quotient-section
projection. -/
theorem sectionsComparison_fac (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    ∀ s : M.sections,
      limit.π (positiveSectionsSystem I M) (op n) (sectionsComparison I M s) =
        sectionsProjection I M n s := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
