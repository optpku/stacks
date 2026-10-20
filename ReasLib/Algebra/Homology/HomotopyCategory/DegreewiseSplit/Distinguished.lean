module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Distinguished degreewise-split triangles

This leaf exposes the forward-use API for mathlib's characterization of distinguished triangles
in the homotopy category by degreewise-split short complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexShape HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- A degreewise splitting of a short complex determines a distinguished triangle in the
homotopy category. -/
@[stacks 09P6 "degreewise-split short complexes give distinguished triangles"]
theorem trianglehOfDegreewiseSplit_distinguished
    (S : ShortComplex (CochainComplex C ℤ))
    (splitting : ∀ n : ℤ, (S.map (eval C (up ℤ) n)).Splitting) :
    trianglehOfDegreewiseSplit S splitting ∈
      distTriang (HomotopyCategory C (up ℤ)) := sorry

end CochainComplex
