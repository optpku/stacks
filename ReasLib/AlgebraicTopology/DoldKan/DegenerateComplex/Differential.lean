/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateSubobject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise degenerate complexes

This leaf owns the alternating-face differential restricted to degreewise degenerate subobjects,
the resulting chain complex, and its canonical inclusion.

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasZeroObject C] [HasBinaryCoproducts C] [HasImages C]

namespace degenerateComplex

/-- The alternating-face differential maps the degree-`n + 1` degenerate subobject into the
degree-`n` degenerate subobject. -/
@[stacks 019A "degenerate differential factorization"]
theorem d.factors (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors
      ((degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n) := sorry

/-- The differential induced on the degreewise degenerate subobjects. -/
@[stacks 019A "degenerate differential"]
def d (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U (n + 1) : C) ⟶ (degenerateSubobject U n : C) :=
  (degenerateSubobject U n).factorThru
    ((degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n)
    (d.factors U n)

/-- The induced degenerate differential agrees after inclusion with the alternating-face
differential. -/
@[reassoc, stacks 019A "degenerate differential inclusion formula"]
theorem d.arrow (U : SimplicialObject C) (n : ℕ) :
    d U n ≫ (degenerateSubobject U n).arrow =
      (degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n := sorry

/-- Consecutive induced degenerate differentials compose to zero. -/
@[stacks 019A "degenerate differential squares to zero"]
theorem d.squared (U : SimplicialObject C) (n : ℕ) :
    d U (n + 1) ≫ d U n = 0 := sorry

end degenerateComplex

/-- The degenerate subcomplex `D(U)` of the alternating-face complex of a simplicial object. -/
@[stacks 019A "degenerate subcomplex"]
def degenerateComplex (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n ↦ (degenerateSubobject U n : C))
    (degenerateComplex.d U) (degenerateComplex.d.squared U)

@[inherit_doc]
scoped[DoldKan] notation "D[" X "]" => AlgebraicTopology.DoldKan.degenerateComplex X

namespace degenerateComplex

/-- The degree-`n` object of the degenerate complex is the degreewise degenerate subobject. -/
@[simp, stacks 019A "degenerate complex object formula"]
theorem obj_X (U : SimplicialObject C) (n : ℕ) :
    D[U].X n = (degenerateSubobject U n : C) := sorry

/-- The adjacent differential of the degenerate complex is the induced degenerate differential. -/
@[stacks 019A "degenerate complex differential formula"]
theorem obj_d (U : SimplicialObject C) (n : ℕ) :
    D[U].d (n + 1) n = d U n := sorry

/-- The degreewise subobject inclusions commute with every relevant differential. -/
@[stacks 019A "degenerate inclusion commutes with differentials"]
theorem ι.comm (U : SimplicialObject C) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    (degenerateSubobject U i).arrow ≫ (K[U]).d i j =
      (D[U]).d i j ≫ (degenerateSubobject U j).arrow := sorry

/-- The inclusion of `D(U)` into the alternating-face complex `K(U)`. -/
@[stacks 019A "degenerate subcomplex inclusion"]
def ι (U : SimplicialObject C) : D[U] ⟶ K[U] where
  f n := (degenerateSubobject U n).arrow
  comm' := ι.comm U

/-- The degree-`n` component of the inclusion of the degenerate complex is the subobject arrow. -/
@[simp, stacks 019A "degenerate inclusion component"]
theorem ι.f (U : SimplicialObject C) (n : ℕ) :
    (ι U).f n = (degenerateSubobject U n).arrow := sorry

end degenerateComplex

end AlgebraicTopology.DoldKan
