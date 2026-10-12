/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential colimits in Grothendieck abelian categories

The standard `IsGrothendieckAbelian` owner records filtered colimits and `AB5` at the category's
own universe size.  Sequential inverse-system APIs use the small shape `ℕ`; these instances are the
single shared universe-shrink bridge needed by that API. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-- A Grothendieck abelian category has colimits for the small sequential shape. -/
@[stacks 079B "small sequential colimits in a Grothendieck abelian category"]
noncomputable instance IsGrothendieckAbelian.hasSequentialColimits
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] : HasColimitsOfShape ℕ C := by
  let _ : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0} C
  infer_instance

/-- A Grothendieck abelian category has exact colimits for the small sequential shape. -/
@[stacks 079B "exact small sequential colimits in a Grothendieck abelian category"]
noncomputable instance IsGrothendieckAbelian.hasExactSequentialColimits
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] : HasExactColimitsOfShape ℕ C := by
  let _ : HasFilteredColimitsOfSize.{0, 0} C := hasFilteredColimitsOfSize_shrink
  let _ : AB5OfSize.{0, 0} C := AB5OfSize_shrink.{0, 0, w, w, v, u} (C := C)
  infer_instance

end CategoryTheory
