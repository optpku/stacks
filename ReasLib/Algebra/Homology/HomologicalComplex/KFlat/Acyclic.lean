/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cycles of acyclic K-flat complexes

In an abelian monoidal category whose tensor product is right exact, the cycles of an acyclic,
termwise-flat K-flat cochain complex are flat.  This is the category-level owner; module-sheaf
files only provide source-facing specializations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace HomologicalComplex.IsKFlat

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ X : C, PreservesFiniteColimits (tensorRight X)]

/-- Stacks `0G7C`, category-level form: every cycle of an acyclic, termwise-flat K-flat
cochain complex is flat. -/
@[stacks 0G7C "categorical owner"]
theorem isFlat_cycles {K : CochainComplex C ℤ}
    (hK : K.IsKFlat) (hAcyclic : K.Acyclic) (hFlat : K.IsTermwiseFlat) (n : ℤ) :
    IsFlat (K.cycles n) := sorry

/-- The raw-kernel view of `IsKFlat.isFlat_cycles`, obtained through the canonical comparison
between cycles and the kernel of the outgoing differential. -/
theorem isFlat_kernel_dFrom {K : CochainComplex C ℤ}
    (hK : K.IsKFlat) (hAcyclic : K.Acyclic) (hFlat : K.IsTermwiseFlat) (n : ℤ) :
    IsFlat (kernel (K.dFrom n)) := sorry

end HomologicalComplex.IsKFlat
