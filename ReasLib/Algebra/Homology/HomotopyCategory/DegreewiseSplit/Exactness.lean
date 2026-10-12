/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Admissible
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exactness through a degreewise-split middle row

The canonical input is a bundled existence statement `Nonempty (∀ n, Splitting)`.  A pointwise
existence bridge is retained for source-facing developments, but downstream consumers can pass a
single selected splitting family to the core theorem.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive ComplexShape HomologicalComplex

universe v u

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V] [HasBinaryBiproducts V]

namespace DegreewiseSplit.HomotopyCategory

/-- A composite through the middle term of a degreewise-split short complex vanishes in the
homotopy category when it vanishes against the two neighboring maps. -/
@[stacks 086L "exactness through a degreewise-split middle row"]
theorem comp_zero_of_splitting
    {S : ShortComplex (CochainComplex V ℤ)}
    (hσ : Nonempty (∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting))
    {X Y : CochainComplex V ℤ}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map S.g = 0)
    (hb' : (HomotopyCategory.quotient V (up ℤ)).map S.f ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0) :
    (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0 := sorry

/-- The exactness criterion consumes the choice-free degreewise-split property directly. -/
@[stacks 086L "choice-free degreewise-split exactness"]
theorem comp_zero
    {S : ShortComplex (CochainComplex V ℤ)}
    (hS : S.IsDegreewiseSplit)
    {X Y : CochainComplex V ℤ}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map S.g = 0)
    (hb' : (HomotopyCategory.quotient V (up ℤ)).map S.f ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0) :
    (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0 := sorry

/-- Pointwise degreewise-splitting is a source-facing form of the bundled exactness criterion. -/
@[stacks 086L "pointwise degreewise-split exactness bridge"]
theorem comp_zero_of_termwise
    {S : ShortComplex (CochainComplex V ℤ)}
    (hσ : ∀ n : ℤ, Nonempty ((S.map (eval V (up ℤ) n)).Splitting))
    {X Y : CochainComplex V ℤ}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map S.g = 0)
    (hb' : (HomotopyCategory.quotient V (up ℤ)).map S.f ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0) :
    (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0 := sorry

/-- The exactness criterion applies directly to admissibly short-exact middle rows. -/
@[stacks 086L "admissible short-exact middle row exactness"]
theorem comp_zero_of_admissible
    {S : ShortComplex (CochainComplex V ℤ)}
    (hS : IsAdmissibleShortExact (forgetToGraded V) S)
    {X Y : CochainComplex V ℤ}
    {b : X ⟶ S.X₂} {b' : S.X₂ ⟶ Y}
    (hb : (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map S.g = 0)
    (hb' : (HomotopyCategory.quotient V (up ℤ)).map S.f ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0) :
    (HomotopyCategory.quotient V (up ℤ)).map b ≫
        (HomotopyCategory.quotient V (up ℤ)).map b' = 0 := sorry

end DegreewiseSplit.HomotopyCategory

end CochainComplex
