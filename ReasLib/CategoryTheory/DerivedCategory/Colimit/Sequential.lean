/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.CountableCoproduct
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Countable
public import ReasLib.CategoryTheory.Limits.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Construction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Colimits in Derived Categories

@stack 0949

For an abelian category with exact sequential colimits, the termwise colimit
of a sequence of cochain complexes presents the sequential homotopy colimit
of their derived images.  The cocone map, connecting morphism, presentation,
and intrinsic predicate are exposed separately.
-/

open CategoryTheory.Limits
open CategoryTheory.Limits.Sequential
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Limits.CountableFromSequential

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.SequentialColimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{w} A]
variable [HasColimitsOfShape ℕ A]

variable [HasExactColimitsOfShape ℕ A]

variable (S : ℕ ⥤ CochainComplex A ℤ)

/-- The canonical map from the coproduct of the derived terms to the derived
image of the termwise colimit. -/
@[stacks 0949]
noncomputable def toCocone :
    ∐ (fun n ↦ DerivedCategory.Q.obj (S.obj n)) ⟶
      DerivedCategory.Q.obj (colimit S) :=
  (PreservesCoproduct.iso DerivedCategory.Q S.obj).inv ≫
    DerivedCategory.Q.map (Limits.Sigma.desc (colimit.ι S))

/-- The connecting morphism in the canonical telescope triangle for the
termwise colimit. -/
@[stacks 0949]
noncomputable def connecting :
    DerivedCategory.Q.obj (colimit S) ⟶
      (∐ fun n ↦ DerivedCategory.Q.obj (S.obj n))⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ (telescopeMap_shortExact S) ≫
    ((PreservesCoproduct.iso DerivedCategory.Q S.obj).hom⟦(1 : ℤ)⟧')

/-- The canonical telescope triangle presenting the derived image of the
termwise colimit. -/
@[stacks 0949]
noncomputable def triangle : Triangle (DerivedCategory A) :=
  Triangle.mk (telescopeMap (S ⋙ DerivedCategory.Q))
    (toCocone S) (connecting S)

/-- Stacks 0949: the canonical termwise-colimit telescope triangle is
distinguished. -/
@[stacks 0949]
theorem distinguished : triangle S ∈ distTriang (DerivedCategory A) := sorry

/-- A concrete telescope presentation of the derived image of a termwise
sequential colimit. -/
@[stacks 0949]
noncomputable def presentation :
    HomotopyColimit.Presentation (S ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (colimit S)) :=
  HomotopyColimit.Presentation.ofCoproductTriangle
    (toCocone S) (connecting S) (distinguished S)

/-- The `n`th presentation leg is the derived image of the corresponding
termwise colimit map. -/
@[simp]
theorem presentation.ι (n : ℕ) :
    (presentation S).ι n = DerivedCategory.Q.map (colimit.ι S n) := sorry

/-- Stacks 0949 (Lemma 13.33.7): the derived image of the termwise colimit is
a homotopy colimit of the derived sequence. -/
@[stacks 0949, stacks 0CRL "sequential colimit as a homotopy colimit"]
theorem isOf :
    HomotopyColimit.IsOf (S ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (colimit S)) := sorry

end CategoryTheory.DerivedCategory.SequentialColimit
