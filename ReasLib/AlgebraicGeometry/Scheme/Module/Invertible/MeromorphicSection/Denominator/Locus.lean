/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.RegularAt
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator

/-!
# Regularity loci of meromorphic sections

The open complement of the denominator ideal of a meromorphic section is its
pointwise regularity locus.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The complement of an ideal identified with the denominator ideal of a
meromorphic section consists exactly of the points where the section is regular. -/
theorem mem_openComplement_iff_isRegularAt_of_eq_denominatorIdeal
    (I : X.IdealSheafData) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hI : I.toSubobject = Scheme.denominatorIdealSheaf ℒ s) (x : X) :
    x ∈ I.openComplement ↔
      LocallyRingedSpace.MeromorphicSection.IsRegularAt s x := sorry

/-- The complement of an ideal identified with the denominator ideal is the
greatest open set on which the corresponding meromorphic section is regular. -/
theorem openComplement_isGreatest_regularAt_of_eq_denominatorIdeal
    (I : X.IdealSheafData) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hI : I.toSubobject = Scheme.denominatorIdealSheaf ℒ s) :
    IsGreatest
      {U : X.Opens |
        ∀ x : X, x ∈ U →
          LocallyRingedSpace.MeromorphicSection.IsRegularAt s x}
      I.openComplement := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
