module

public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Admissible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative flatness for monoid objects in cochain complexes

This file owns the presentation-independent fixed-base conditions used for good differential
graded modules.  An algebra is a monoid object in cochain complexes and a right DG module is a
one-sided bimodule.  Graded flatness is measured after the canonical monoidal functor forgetting
the differential, while K-flatness is measured by the balanced tensor product itself.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable [MonoidalCategory (CochainComplex C ℤ)]

variable {A : Mon (CochainComplex C ℤ)}

section

variable [MonoidalCategory (GradedObject ℤ C)]
variable [(CochainComplex.forgetToGraded C).LaxMonoidal]
variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- A right module over a cochain monoid is graded-flat when its underlying graded right module
is flat for the balanced tensor product. -/
@[stacks 0FSA "generic graded relative flatness"]
def IsGradedFlat (M : RightModule A) : Prop :=
  IsFlat ((forgetToGradedRight A).obj M)

/-- Graded-flat right modules over a cochain monoid as an object property. -/
abbrev gradedFlatObjects (A : Mon (CochainComplex C ℤ)) :
    ObjectProperty (RightModule A) :=
  fun M ↦ IsGradedFlat M

/-- Generic graded relative flatness is flatness of the transported graded bimodule. -/
theorem isGradedFlat_iff (M : RightModule A) :
    IsGradedFlat M ↔ IsFlat ((forgetToGradedRight A).obj M) := sorry

end

section

variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- A right module over a cochain monoid is relatively K-flat when balanced tensoring with every
acyclic left module produces an acyclic cochain complex. -/
@[stacks 0FSA "generic relative K-flatness"]
def IsKFlat (M : RightModule A) : Prop :=
  ∀ N : LeftModule A, HomologicalComplex.Acyclic N.X →
    HomologicalComplex.Acyclic (tensor M N)

/-- Relatively K-flat right modules over a cochain monoid as an object property. -/
abbrev kFlatObjects (A : Mon (CochainComplex C ℤ)) :
    ObjectProperty (RightModule A) :=
  fun M ↦ IsKFlat M

/-- Generic relative K-flatness is preservation of acyclicity by balanced tensoring. -/
theorem isKFlat_iff (M : RightModule A) :
    IsKFlat M ↔
      ∀ N : LeftModule A, HomologicalComplex.Acyclic N.X →
        HomologicalComplex.Acyclic (tensor M N) := sorry

end

section

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

/-- The fixed-base goodness conditions for a right module over a cochain monoid. -/
@[stacks 0FSA "generic goodness conditions at a fixed base"]
def IsGoodAtBase (M : RightModule A) : Prop :=
  IsGradedFlat M ∧ IsKFlat M

/-- Right modules satisfying both fixed-base goodness conditions as an object property. -/
abbrev goodAtBaseObjects (A : Mon (CochainComplex C ℤ)) :
    ObjectProperty (RightModule A) :=
  fun M ↦ IsGoodAtBase M

/-- Fixed-base goodness is exactly graded relative flatness together with relative K-flatness. -/
theorem isGoodAtBase_iff (M : RightModule A) :
    IsGoodAtBase M ↔ IsGradedFlat M ∧ IsKFlat M := sorry

end

namespace LeftModule

section

variable [MonoidalCategory (GradedObject ℤ C)]
variable [(CochainComplex.forgetToGraded C).LaxMonoidal]
variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- A left module over a cochain monoid is graded-flat when its underlying graded left module is
flat for the balanced tensor product. -/
@[stacks 0FSA "generic graded relative flatness for left modules"]
def IsGradedFlat (N : LeftModule A) : Prop :=
  IsFlat ((forgetToGradedLeft A).obj N)

/-- Graded-flat left modules over a cochain monoid as an object property. -/
@[stacks 0FSA "generic graded-flat left module object property"]
abbrev gradedFlatObjects (A : Mon (CochainComplex C ℤ)) :
    ObjectProperty (LeftModule A) :=
  fun N ↦ IsGradedFlat N

/-- Left graded relative flatness is flatness of the transported graded left module. -/
@[stacks 0FSA "left graded relative flatness criterion"]
theorem isGradedFlat_iff (N : LeftModule A) :
    IsGradedFlat N ↔ IsFlat ((forgetToGradedLeft A).obj N) := sorry

end

section

variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- A left module over a cochain monoid is relatively K-flat when balanced tensoring every
acyclic right module with it produces an acyclic cochain complex. -/
@[stacks 0FSA "generic relative K-flatness for left modules"]
def IsKFlat (N : LeftModule A) : Prop :=
  ∀ M : RightModule A, HomologicalComplex.Acyclic M.X →
    HomologicalComplex.Acyclic (tensor N M)

/-- Relatively K-flat left modules over a cochain monoid as an object property. -/
@[stacks 0FSA "generic K-flat left module object property"]
abbrev kFlatObjects (A : Mon (CochainComplex C ℤ)) :
    ObjectProperty (LeftModule A) :=
  fun N ↦ IsKFlat N

/-- Left relative K-flatness is preservation of acyclicity by balanced tensoring. -/
@[stacks 0FSA "left relative K-flatness criterion"]
theorem isKFlat_iff (N : LeftModule A) :
    IsKFlat N ↔
      ∀ M : RightModule A, HomologicalComplex.Acyclic M.X →
        HomologicalComplex.Acyclic (tensor N M) := sorry

end

section

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

/-- The fixed-base goodness conditions for a left module over a cochain monoid. -/
@[stacks 0FSA "generic goodness conditions for left modules at a fixed base"]
def IsGoodAtBase (N : LeftModule A) : Prop :=
  IsGradedFlat N ∧ IsKFlat N

/-- Left modules satisfying both fixed-base goodness conditions as an object property. -/
@[stacks 0FSA "generic good left module object property at a fixed base"]
abbrev goodAtBaseObjects (A : Mon (CochainComplex C ℤ)) :
    ObjectProperty (LeftModule A) :=
  fun N ↦ IsGoodAtBase N

/-- Left fixed-base goodness is graded relative flatness together with relative K-flatness. -/
@[stacks 0FSA "left fixed-base goodness criterion"]
theorem isGoodAtBase_iff (N : LeftModule A) :
    IsGoodAtBase N ↔ IsGradedFlat N ∧ IsKFlat N := sorry

end

end LeftModule

end CategoryTheory.Bimod

end
