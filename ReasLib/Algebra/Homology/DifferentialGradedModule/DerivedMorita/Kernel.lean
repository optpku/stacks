module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.SelfExt
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morita Kernels for Differential Graded Modules

This leaf owns the compact-generator and self-extension predicate used to recognize a DG
bimodule as a Morita kernel.  The realization theorem for transporting kernels along an arbitrary
equivalence lives in the sibling `DerivedMorita` leaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v uD vD

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

/-- A differential graded bimodule is a Morita kernel after a chosen shift-compatible functor
when its image is compact, weakly generates the target, and has the expected self-extensions. -/
@[stacks 09SA "Morita kernel after a chosen localization",
  stacks 09S7 "compact-generator Morita kernel"]
structure IsMoritaKernelFor {D : Type uD} [Category.{vD} D]
    [Preadditive D] [Linear R D] [HasShift D ℤ]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R] : Prop where
  /-- The localized right module is compact. -/
  isCompact : IsCompactObject (Q.obj N.rightHomotopyObject)
  /-- The localized right module weakly generates the target category. -/
  isWeakGenerator : IsWeakGenerator (Q.obj N.rightHomotopyObject)
  /-- The left action computes every shifted self-extension after localization. -/
  hasSelfExtComparison : N.HasSelfExtComparisonFor Q

/-- The three defining conditions for a Morita kernel after a chosen localization. -/
@[stacks 09SA "compact-generator and self-extension criterion for a Morita kernel"]
theorem isMoritaKernelFor_iff {D : Type uD} [Category.{vD} D]
    [Preadditive D] [Linear R D] [HasShift D ℤ]
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (Q : K R (DifferentialGradedModule.{u, v} B) ⥤ D)
    [Q.CommShift ℤ] [Q.Additive] [Q.Linear R] :
    N.IsMoritaKernelFor Q ↔
      IsCompactObject (Q.obj N.rightHomotopyObject) ∧
        IsWeakGenerator (Q.obj N.rightHomotopyObject) ∧
          N.HasSelfExtComparisonFor Q := sorry

/-- A Morita kernel in the canonical derived category of the right-hand algebra. -/
@[stacks 09SA "Morita kernel in the canonical differential graded derived category",
  stacks 09S7 "canonical compact-generator Morita kernel"]
abbrev IsMoritaKernel (N : DifferentialGradedBimodule.{u, v, v, v} A B) : Prop :=
  N.IsMoritaKernelFor (DifferentialGradedModule.Derived.Q.{u, v} B)

/-- The compactness, generation, and self-extension conditions defining a canonical Morita
kernel. -/
@[stacks 09S7 "compact-generator and self-extension criterion for a canonical Morita kernel"]
theorem isMoritaKernel_iff (N : DifferentialGradedBimodule.{u, v, v, v} A B) :
    N.IsMoritaKernel ↔
      IsCompactObject N.rightDerivedObject ∧
        IsWeakGenerator N.rightDerivedObject ∧ N.HasSelfExtComparison := sorry

end DifferentialGradedBimodule
