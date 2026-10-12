/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.TermwiseFlat
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat homotopy objects with flat terms

The object property in this file isolates the good models used to construct unbounded left
derived functors.  Keeping termwise flatness separate from K-flatness is essential: many
functors preserve quasi-isomorphisms between these good models without preserving arbitrary
K-flat complexes.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.HomotopyCategory.KFlat

variable (C : Type u) [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- The homotopy objects represented by K-flat complexes whose terms are flat. -/
@[stacks 06YY "K-flat termwise-flat models"]
def termwiseFlat : ObjectProperty (HomotopyCategory C (up ℤ)) :=
  fun K ↦ HomologicalComplex.KFlat.termwiseFlat (up ℤ) K.as

/-- The full subcategory of K-flat homotopy objects represented by complexes with flat terms. -/
abbrev TermwiseFlat := (termwiseFlat C).FullSubcategory

namespace TermwiseFlat

/-- Membership means exactly K-flatness together with termwise flatness of the representative. -/
theorem mem_iff (K : HomotopyCategory C (up ℤ)) :
    termwiseFlat C K ↔
      K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K.as := sorry

/-- A good flat model is K-flat. -/
theorem isKFlat {K : HomotopyCategory C (up ℤ)}
    (hK : termwiseFlat C K) : K.IsKFlat := sorry

/-- The representative of a good flat model is termwise flat. -/
theorem isTermwiseFlat {K : HomotopyCategory C (up ℤ)}
    (hK : termwiseFlat C K) :
    HomologicalComplex.IsTermwiseFlat K.as := sorry

end TermwiseFlat
end CategoryTheory.HomotopyCategory.KFlat
