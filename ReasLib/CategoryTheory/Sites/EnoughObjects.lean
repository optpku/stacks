module

public import ReasLib.CategoryTheory.Sites.Family.Covering
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
      ∀ U : C, ∃ U' : SemiRepresentableFamily.Over.{max u v} U,
        U'.toSieve ∈ J U ∧ ∀ i : U'.index, P (U'.obj i).left := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Coverage

variable {C : Type u} [Category.{v} C] (K : Coverage C)

/-- Situation 18.30.5 (0937) (1): a chosen-cover site has enough objects with property `P`
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
      ∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over.{max u v} U,
        𝒰.toPresieve ∈ K U ∧ ∀ i : 𝒰.index, P (𝒰.obj i).left := sorry

/-- A chosen-cover family is covering for the generated Grothendieck topology, so enough
objects for a coverage give enough objects for its associated topology. -/
theorem toGrothendieck {P : ObjectProperty C}
    (hP : K.HasEnoughObjectsWithProperty P) :
    K.toGrothendieck.HasEnoughObjectsWithProperty P := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.Coverage
