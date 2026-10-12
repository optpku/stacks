/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Covers by objects with a property

The predicate in this module is the neutral site-theoretic owner for statements saying that every
object has a cover by objects satisfying a fixed property.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A Grothendieck topology has enough objects with property `P` when every object has a covering
presieve whose generating arrows have sources satisfying `P`.  This is the sieve-saturated
companion to the chosen-cover predicate. -/
@[stacks 0937 "(1), sieve-saturated specialization", stacks 090L "(3)"]
def HasEnoughObjectsWithProperty (P : ObjectProperty C) : Prop :=
  ∀ U : C, ∃ R : Presieve U,
    Sieve.generate R ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), R f → P V

namespace HasEnoughObjectsWithProperty

/-- A site has enough objects with property `P` exactly when every object admits an explicit
covering family all of whose members satisfy `P`. -/
theorem iff_existsCoveringFamily (P : ObjectProperty C) :
    J.HasEnoughObjectsWithProperty P ↔
      ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
        Sieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ J U ∧
          ∀ i : families.index, P (families.obj i).left := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Coverage

variable {C : Type u} [Category.{v} C] (K : Coverage C)

/-- A chosen-cover site has enough objects with property `P`
when every object has a selected covering family whose sources satisfy `P`. -/
@[stacks 0937 "(1)"]
def HasEnoughObjectsWithProperty (P : ObjectProperty C) : Prop :=
  ∀ U : C, ∃ R : Presieve U,
    R ∈ K U ∧ ∀ {V : C} (f : V ⟶ U), R f → P V

namespace HasEnoughObjectsWithProperty

/-- The explicit fixed-target-family characterization of having enough objects with a property
for a chosen coverage. -/
theorem iff_existsCoveringFamily (P : ObjectProperty C) :
    K.HasEnoughObjectsWithProperty P ↔
      ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
        Presieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ K U ∧
          ∀ i : families.index, P (families.obj i).left := sorry

/-- A chosen-cover family is covering for the generated Grothendieck topology, so enough
objects for a coverage give enough objects for its associated topology. -/
theorem toGrothendieck {P : ObjectProperty C}
    (hP : K.HasEnoughObjectsWithProperty P) :
    K.toGrothendieck.HasEnoughObjectsWithProperty P := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.Coverage
