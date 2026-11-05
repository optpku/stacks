module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Basic

/-!
# Closed subtopoi

Closed subtopoi are indexed by the existing bundled category of subterminal
objects.  Naming the corresponding object property makes the product-
projection criterion available independently of the existential source
definition.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology

/-- The object property cut out by the product projection from a subterminal
sheaf `U`. -/
def closedSubtopos
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (U : Subterminals (Sheaf J (Type w))) : ObjectProperty (Sheaf J (Type w)) :=
  fun G ↦ IsIso (prod.fst : U.1 ⨯ G ⟶ U.1)

/-- A closed subtopos is the object property associated to one subterminal sheaf by
`closedSubtopos`. -/
@[stacks 08LZ]
def IsClosedSubtopos
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ U : Subterminals (Sheaf J (Type w)), P = closedSubtopos J U

/-- A closed-subtopos predicate supplies its bundled subterminal
presentation. -/
theorem IsClosedSubtopos.exists_subterminal
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {P : ObjectProperty (Sheaf J (Type w))} (hP : IsClosedSubtopos P) :
    ∃ U : Subterminals (Sheaf J (Type w)), P = closedSubtopos J U := sorry

/-- The product-projection condition defining a closed subtopos determines a subtopos. -/
@[stacks 08LY]
theorem IsClosedSubtopos.isSubtopos
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {P : ObjectProperty (Sheaf J (Type w))} (hP : IsClosedSubtopos P) :
    IsSubtopos.{u, max u v w, v, max u v w, w} J P := sorry

end CategoryTheory.GrothendieckTopology
