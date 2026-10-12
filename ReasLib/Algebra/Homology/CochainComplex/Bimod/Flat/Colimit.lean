/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Flat
public import ReasLib.Algebra.Homology.HomologicalComplex.Acyclic.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of flat modules over cochain monoids

This file owns the shape-polymorphic colimit API for relative graded flatness, relative
K-flatness, and their fixed-base conjunction.  The hypotheses separate the three mechanisms used
by the statements: existence of module colimits, exactness in the ambient category, and
cocontinuity of the relevant forgetful and balanced tensor functors.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v uI vI

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory (CochainComplex C ℤ)]
variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable [MonoidalCategory (GradedObject ℤ C)]
variable [(CochainComplex.forgetToGraded C).LaxMonoidal]
variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A : Mon (CochainComplex C ℤ)}

namespace IsGradedFlat

section Colimit

variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I (RightModule A)]
variable [HasColimitsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape I (GradedObject ℤ C)]
variable [PreservesColimitsOfShape I (forgetToGradedRight A)]
variable [∀ N : LeftModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape I (LeftModule.tensorFunctor N)]

/-- An exact colimit of graded-flat right modules over a cochain monoid is graded-flat. -/
@[stacks 0FSD "generic graded-flat exact colimits"]
theorem colimit_of_exact (F : I ⥤ RightModule A)
    (hF : ∀ i, IsGradedFlat (F.obj i)) :
    IsGradedFlat (colimit F) := sorry

/-- A filtered colimit of graded-flat right modules over a cochain monoid is graded-flat whenever
the relevant filtered colimits are exact and preserved by the structural functors. -/
@[stacks 0FSD "generic graded-flat filtered colimits"]
theorem colimit_of_isFiltered [IsFiltered I] (F : I ⥤ RightModule A)
    (hF : ∀ i, IsGradedFlat (F.obj i)) :
    IsGradedFlat (colimit F) := sorry

end Colimit

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I (RightModule A)]
variable [HasCoproductsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape (Discrete I) (GradedObject ℤ C)]
variable [PreservesColimitsOfShape (Discrete I) (forgetToGradedRight A)]
variable [∀ N : LeftModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape (Discrete I) (LeftModule.tensorFunctor N)]

/-- A coproduct of graded-flat right modules over a cochain monoid is graded-flat whenever the
ambient coproduct is exact and the structural functors preserve it. -/
@[stacks 0FSD "generic graded-flat coproducts"]
theorem coproduct (F : I → RightModule A) (hF : ∀ i, IsGradedFlat (F i)) :
    IsGradedFlat (∐ F) := sorry

end Coproduct

end IsGradedFlat

namespace IsKFlat

section Colimit

variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I (RightModule A)]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [∀ N : LeftModule A,
  PreservesColimitsOfShape I (LeftModule.tensorFunctor N)]

/-- An exact colimit of relatively K-flat right modules over a cochain monoid is relatively
K-flat. -/
@[stacks 0FSD "generic K-flat exact colimits"]
theorem colimit_of_exact (F : I ⥤ RightModule A)
    (hF : ∀ i, IsKFlat (F.obj i)) :
    IsKFlat (colimit F) := sorry

/-- A filtered colimit of relatively K-flat right modules over a cochain monoid is relatively
K-flat whenever the relevant filtered colimits are exact and preserved by balanced tensoring. -/
@[stacks 0FSD "generic K-flat filtered colimits"]
theorem colimit_of_isFiltered [IsFiltered I] (F : I ⥤ RightModule A)
    (hF : ∀ i, IsKFlat (F.obj i)) :
    IsKFlat (colimit F) := sorry

end Colimit

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I (RightModule A)]
variable [HasCoproductsOfShape I C]
variable [HasExactColimitsOfShape (Discrete I) C]
variable [∀ N : LeftModule A,
  PreservesColimitsOfShape (Discrete I) (LeftModule.tensorFunctor N)]

/-- A coproduct of relatively K-flat right modules over a cochain monoid is relatively K-flat
whenever ambient coproducts are exact and balanced tensoring preserves them. -/
@[stacks 0FSD "generic K-flat coproducts"]
theorem coproduct (F : I → RightModule A) (hF : ∀ i, IsKFlat (F i)) :
    IsKFlat (∐ F) := sorry

end Coproduct

end IsKFlat

namespace IsGoodAtBase

section Colimit

variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I (RightModule A)]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [HasColimitsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape I (GradedObject ℤ C)]
variable [PreservesColimitsOfShape I (forgetToGradedRight A)]
variable [∀ N : LeftModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape I (LeftModule.tensorFunctor N)]
variable [∀ N : LeftModule A,
  PreservesColimitsOfShape I (LeftModule.tensorFunctor N)]

/-- An exact colimit of fixed-base-good right modules over a cochain monoid remains
fixed-base-good. -/
@[stacks 0FSD "generic fixed-base-good exact colimits"]
theorem colimit_of_exact (F : I ⥤ RightModule A)
    (hF : ∀ i, IsGoodAtBase (F.obj i)) :
    IsGoodAtBase (colimit F) := sorry

/-- A filtered colimit of fixed-base-good right modules over a cochain monoid remains
fixed-base-good whenever both defining flatness conditions commute with that colimit. -/
@[stacks 0FSD "generic fixed-base-good filtered colimits"]
theorem colimit_of_isFiltered [IsFiltered I] (F : I ⥤ RightModule A)
    (hF : ∀ i, IsGoodAtBase (F.obj i)) :
    IsGoodAtBase (colimit F) := sorry

end Colimit

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I (RightModule A)]
variable [HasCoproductsOfShape I C]
variable [HasExactColimitsOfShape (Discrete I) C]
variable [HasCoproductsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape (Discrete I) (GradedObject ℤ C)]
variable [PreservesColimitsOfShape (Discrete I) (forgetToGradedRight A)]
variable [∀ N : LeftModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape (Discrete I) (LeftModule.tensorFunctor N)]
variable [∀ N : LeftModule A,
  PreservesColimitsOfShape (Discrete I) (LeftModule.tensorFunctor N)]

/-- A coproduct of fixed-base-good right modules over a cochain monoid remains fixed-base-good
whenever both ambient coproducts are exact and the structural functors preserve them. -/
@[stacks 0FSD "generic fixed-base-good coproducts"]
theorem coproduct (F : I → RightModule A) (hF : ∀ i, IsGoodAtBase (F i)) :
    IsGoodAtBase (∐ F) := sorry

end Coproduct

end IsGoodAtBase

namespace LeftModule

namespace IsGradedFlat

section Colimit

variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I (LeftModule A)]
variable [HasColimitsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape I (GradedObject ℤ C)]
variable [PreservesColimitsOfShape I (forgetToGradedLeft A)]
variable [∀ M : RightModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape I (CategoryTheory.Bimod.tensorFunctor M)]

/-- An exact colimit of graded-flat left modules over a cochain monoid is graded-flat. -/
@[stacks 0FSD "generic left graded-flat exact colimits"]
theorem colimit_of_exact (F : I ⥤ LeftModule A)
    (hF : ∀ i, LeftModule.IsGradedFlat (F.obj i)) :
    LeftModule.IsGradedFlat (colimit F) := sorry

/-- A filtered colimit of graded-flat left modules over a cochain monoid is graded-flat whenever
the relevant filtered colimits are exact and preserved by the structural functors. -/
@[stacks 0FSD "generic left graded-flat filtered colimits"]
theorem colimit_of_isFiltered [IsFiltered I] (F : I ⥤ LeftModule A)
    (hF : ∀ i, LeftModule.IsGradedFlat (F.obj i)) :
    LeftModule.IsGradedFlat (colimit F) := sorry

end Colimit

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I (LeftModule A)]
variable [HasCoproductsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape (Discrete I) (GradedObject ℤ C)]
variable [PreservesColimitsOfShape (Discrete I) (forgetToGradedLeft A)]
variable [∀ M : RightModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape (Discrete I) (CategoryTheory.Bimod.tensorFunctor M)]

/-- A coproduct of graded-flat left modules over a cochain monoid is graded-flat whenever the
ambient coproduct is exact and the structural functors preserve it. -/
@[stacks 0FSD "generic left graded-flat coproducts"]
theorem coproduct (F : I → LeftModule A)
    (hF : ∀ i, LeftModule.IsGradedFlat (F i)) :
    LeftModule.IsGradedFlat (∐ F) := sorry

end Coproduct

end IsGradedFlat

namespace IsKFlat

section Colimit

variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I (LeftModule A)]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [∀ M : RightModule A,
  PreservesColimitsOfShape I (CategoryTheory.Bimod.tensorFunctor M)]

/-- An exact colimit of relatively K-flat left modules over a cochain monoid is relatively
K-flat. -/
@[stacks 0FSD "generic left K-flat exact colimits"]
theorem colimit_of_exact (F : I ⥤ LeftModule A)
    (hF : ∀ i, LeftModule.IsKFlat (F.obj i)) :
    LeftModule.IsKFlat (colimit F) := sorry

/-- A filtered colimit of relatively K-flat left modules over a cochain monoid is relatively
K-flat whenever the relevant filtered colimits are exact and preserved by balanced tensoring. -/
@[stacks 0FSD "generic left K-flat filtered colimits"]
theorem colimit_of_isFiltered [IsFiltered I] (F : I ⥤ LeftModule A)
    (hF : ∀ i, LeftModule.IsKFlat (F.obj i)) :
    LeftModule.IsKFlat (colimit F) := sorry

end Colimit

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I (LeftModule A)]
variable [HasCoproductsOfShape I C]
variable [HasExactColimitsOfShape (Discrete I) C]
variable [∀ M : RightModule A,
  PreservesColimitsOfShape (Discrete I) (CategoryTheory.Bimod.tensorFunctor M)]

/-- A coproduct of relatively K-flat left modules over a cochain monoid is relatively K-flat
whenever ambient coproducts are exact and balanced tensoring preserves them. -/
@[stacks 0FSD "generic left K-flat coproducts"]
theorem coproduct (F : I → LeftModule A)
    (hF : ∀ i, LeftModule.IsKFlat (F i)) :
    LeftModule.IsKFlat (∐ F) := sorry

end Coproduct

end IsKFlat

namespace IsGoodAtBase

section Colimit

variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I (LeftModule A)]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [HasColimitsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape I (GradedObject ℤ C)]
variable [PreservesColimitsOfShape I (forgetToGradedLeft A)]
variable [∀ M : RightModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape I (CategoryTheory.Bimod.tensorFunctor M)]
variable [∀ M : RightModule A,
  PreservesColimitsOfShape I (CategoryTheory.Bimod.tensorFunctor M)]

/-- An exact colimit of fixed-base-good left modules over a cochain monoid remains
fixed-base-good. -/
@[stacks 0FSD "generic left fixed-base-good exact colimits"]
theorem colimit_of_exact (F : I ⥤ LeftModule A)
    (hF : ∀ i, LeftModule.IsGoodAtBase (F.obj i)) :
    LeftModule.IsGoodAtBase (colimit F) := sorry

/-- A filtered colimit of fixed-base-good left modules over a cochain monoid remains
fixed-base-good whenever both defining flatness conditions commute with that colimit. -/
@[stacks 0FSD "generic left fixed-base-good filtered colimits"]
theorem colimit_of_isFiltered [IsFiltered I] (F : I ⥤ LeftModule A)
    (hF : ∀ i, LeftModule.IsGoodAtBase (F.obj i)) :
    LeftModule.IsGoodAtBase (colimit F) := sorry

end Colimit

section Coproduct

variable {I : Type uI}
variable [HasCoproductsOfShape I (LeftModule A)]
variable [HasCoproductsOfShape I C]
variable [HasExactColimitsOfShape (Discrete I) C]
variable [HasCoproductsOfShape I (GradedObject ℤ C)]
variable [HasExactColimitsOfShape (Discrete I) (GradedObject ℤ C)]
variable [PreservesColimitsOfShape (Discrete I) (forgetToGradedLeft A)]
variable [∀ M : RightModule ((CochainComplex.forgetToGraded C).mapMon.obj A),
  PreservesColimitsOfShape (Discrete I) (CategoryTheory.Bimod.tensorFunctor M)]
variable [∀ M : RightModule A,
  PreservesColimitsOfShape (Discrete I) (CategoryTheory.Bimod.tensorFunctor M)]

/-- A coproduct of fixed-base-good left modules over a cochain monoid remains fixed-base-good
whenever both ambient coproducts are exact and the structural functors preserve them. -/
@[stacks 0FSD "generic left fixed-base-good coproducts"]
theorem coproduct (F : I → LeftModule A)
    (hF : ∀ i, LeftModule.IsGoodAtBase (F i)) :
    LeftModule.IsGoodAtBase (∐ F) := sorry

end Coproduct

end IsGoodAtBase

end LeftModule

end CategoryTheory.Bimod

end
