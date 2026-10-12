/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.CategoryTheory.Monoidal.Flat.Coproduct
public import ReasLib.CategoryTheory.Monoidal.Flat.Zero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise-flat tensor products of complexes

Termwise flatness is closed under totalized tensor products when flat objects are closed under
the small coproducts defining each total degree. The tensor unit is termwise flat in an abelian
monoidal category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w

namespace HomologicalComplex.IsTermwiseFlat

section Tensor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [IsFlat.Coproducts C]
variable {I : Type w} [AddMonoid I] [DecidableEq I]
variable {c : ComplexShape I} [c.TensorSigns]

/-- The totalized tensor product of two termwise-flat complexes is termwise flat. -/
@[stacks 06YY "termwise-flat tensor closure"]
theorem tensor {K L : HomologicalComplex C c} [HasTensor K L]
    (hK : IsTermwiseFlat K) (hL : IsTermwiseFlat L) :
    IsTermwiseFlat (tensorObj K L) := sorry

end Tensor

section Unit

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type w} [AddMonoid I] [DecidableEq I]
variable (c : ComplexShape I) [c.TensorSigns]

/-- The tensor unit complex is termwise flat. -/
@[stacks 06YY "termwise-flat tensor unit"]
theorem tensorUnit :
    IsTermwiseFlat (HomologicalComplex.tensorUnit C c) := sorry

end Unit

end HomologicalComplex.IsTermwiseFlat
